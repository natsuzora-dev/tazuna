import Tazuna.Smt.NameCode
import Tazuna.Smt.Confirm
import Tazuna.Smt.Sha256
import Std.Sync.Semaphore

/-! Running the solver. Each script runs in its own solver process, which reads the script from a file and prints its
answer on stdout; the process boundary contains a solver crash, and a run past its time is killed. This is the one
place that knows the solver is z3: its executable, its command line, and the header lines outside standard SMT-LIB,
its resource limit and its random seeds. -/

namespace Tazuna.Smt

structure Solver where
  path : String
  /-- z3's deterministic resource limit, so the same script gets the same verdict on any machine. prove and generate
  take it from the model (`resource_limit`); this default is smt-check's. -/
  rlimit : Nat := 50000000
  /-- z3's random seeds, fixed so the same script gets the same answer, model included, on every run (Boogie sets
  the same two options). -/
  seed : Nat := 0
  /-- The wall-clock safety net: the process is killed after this many ms, a hundred times what the resource limit
  takes on a laptop, so the resource limit stops z3 first on any machine that runs it. -/
  timeoutMs : Nat := 600000
  /-- Where set, a solver process runs only while it holds one of the gate's permits, which bound the solvers running
  at once whatever number of threads build scripts. -/
  gate : Option Std.Semaphore := none
  /-- The run's wall-clock deadline (`IO.monoMsNow`), from `--timeout`: past it no solver process starts, a running
  one is killed, and the call throws, so the question it served gets no answer rather than a wrong one. -/
  deadline : Option Nat := none
  /-- How many solver processes run, so a run cut off waits for every one it killed (`Solver.drain`). -/
  running : Option (IO.Ref Nat) := none

/-- Whether the run's deadline has passed. -/
def Solver.past (s : Solver) : IO Bool := do
  match s.deadline with
  | some d => return (← IO.monoMsNow) ≥ d
  | none => return false

/-- Waits until no solver process runs: each one past the deadline kills itself within a few milliseconds. -/
def Solver.drain (s : Solver) : IO Unit := do
  if let some r := s.running then
    while (← r.get) > 0 do
      IO.sleep 5

/-- What a solver call throws past the run's deadline. -/
def cutOff : IO.Error := .userError "the run's --timeout passed"

/-- z3 beside the engine's executable, where the launcher puts the z3 it fetched with the engine; else z3 on PATH, as
for an engine built from lean/ that `TAZUNA_ENGINE` names. -/
def Solver.find : IO Solver := do
  let beside := (← IO.appDir) / (if System.Platform.isWindows then "z3.exe" else "z3")
  return { path := if ← beside.pathExists then beside.toString else "z3", running := some (← IO.mkRef 0) }

/-- z3 prints a value with `let` aliases, which values in SMT-LIB's model syntax do not have, beyond depth 5 and for a
part of size 10 or more that occurs twice; both limits are raised so every value prints as a term. -/
def Solver.header (s : Solver) : List String :=
  [s!"(set-option :rlimit {s.rlimit})", s!"(set-option :smt.random_seed {s.seed})",
    s!"(set-option :sat.random_seed {s.seed})", "(set-option :pp.max_depth 4294967295)",
    "(set-option :pp.min_alias_size 4294967295)"]

/-- Runs one script's text: what the solver printed, or why it printed nothing to read. z3 reads a file about twice as
fast as the same text on stdin with `-in`, so the text goes to a temporary file. -/
def Solver.runText (s : Solver) (text : String) : IO (Except Answer String) :=
  IO.FS.withTempFile fun h path => do
    h.putStr text
    h.flush
    runFile path
where
  runFile (path : System.FilePath) : IO (Except Answer String) := do
    let some gate := s.gate | runProcess path
    IO.wait (← gate.acquire).result!
    try runProcess path finally gate.release
  runProcess (path : System.FilePath) : IO (Except Answer String) := do
    -- Counted before the deadline is read, so a process that starts is one `drain` waits for.
    if let some r := s.running then r.modify (· + 1)
    try
      if ← s.past then throw cutOff
      let child ← IO.Process.spawn
        { cmd := s.path, args := #["-smt2", path.toString], stdin := .null, stdout := .piped, stderr := .null }
      let out ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
      let deadline := (← IO.monoMsNow) + s.timeoutMs
      while !(← IO.hasFinished out) && (← IO.monoMsNow) < deadline && !(← s.past) do
        IO.sleep 5
      if !(← IO.hasFinished out) then
        child.kill
        let _ ← child.wait
        if ← s.past then throw cutOff
        return .error (.timeout s.timeoutMs)
      let _ ← child.wait
      match out.get with
      | .ok text => return .ok text
      | .error e => return .error (.unknown s!"the solver's output did not read: {e}")
    finally
      if let some r := s.running then r.modify (· - 1)

/-- What the solver says its version is: the cache keeps each version's answers apart. -/
def Solver.version (s : Solver) : IO String := do
  let out ← IO.Process.output { cmd := s.path, args := #["-version"] }
  return out.stdout.trimAscii.toString

-- A script's answer reports every variable it declares, so the default is never read.
set_option linter.tazuna.silentDefault false in
/-- The values the solver gave, as a model. -/
def modelOf (vs : List (Nat × Val)) : Model :=
  { vars := fun n => (vs.lookup n).getD default, divZero := fun _ => 0, modZero := fun _ => 0,
    selOther := fun _ _ _ _ => default, defs := fun _ => default, funs := fun _ _ => 0 }

/-- Why a script has no text (`Script.shared`): a shared term without a sort, or an assertion holding a reference.
The encoder builds neither, but no theorem states it, so where it happens it is an engine bug, never a spec's
undecided line. -/
def noText : String :=
  "the script has a shared term without a sort or an assertion holding a reference; the encoder builds neither " ++
    "(unproved)"

/-- Runs one script and reads the answer; smt-check's runner, which reads a script without text as unknown. -/
def Solver.run (s : Solver) (script : Script) : IO Answer := do
  let some text := script.text s.header | return .unknown noText
  match ← s.runText text with
  | .ok out => return Answer.parse out
  | .error a => return a

/-- Strings joined so the parts can be read back: each prefixed by its length. -/
def frame (parts : List String) : String := String.join (parts.map fun p => s!"{p.length}:{p}")

/-- A script's text with the cache key its answer is kept under. A key is the SHA-256 of exactly the parts that print
the text, so equal keys mean equal texts unless SHA-256 collides: built only here, by `Script.keyed` and
`ScriptPrefix.ask`. -/
structure Keyed where
  private mk ::
  key : String
  /-- Printed only when the answer is not kept. -/
  text : Unit → String

/-- The script keyed by the SHA-256 of its whole text; none as `Script.text`. -/
def Script.keyed (s : Script) (header : List String) : Option Keyed :=
  (s.text header).map fun t => ⟨Sha256.hex t.toUTF8, fun _ => t⟩

/-- Runs the keyed script, or reads its answer from the cache directory `dir` under its key, as ccache and Bazel key
results by a digest of their inputs, so the cache keeps no script. The text holds the solver's header (resource limit,
seeds) and `dir` is the solver version's, so a raised limit or another z3 asks again. Only a decided answer is kept
(`Answer.decided`): never a timeout nor output that does not read. -/
def Solver.runKeyed (s : Solver) (dir : System.FilePath) (q : Keyed) : IO Answer := do
  let answerFile := dir / (q.key ++ ".answer")
  if ← answerFile.pathExists then
    return Answer.parse (← IO.FS.readFile answerFile)
  match ← s.runText (q.text ()) with
  | .error a => return a
  | .ok out =>
    let a := Answer.parse out
    if a.decided then
      IO.FS.createDirAll dir
      -- A run stopped mid-write leaves no answer file to misread.
      let partFile := answerFile.withExtension "part"
      IO.FS.writeFile partFile out
      IO.FS.rename partFile answerFile
    return a

/-- The answer with each name the solver gave as a code (`Script.sent`) read as its name. -/
def Answer.uncode (ids : Option Nat) (a : Answer) : Answer :=
  match ids, a with
  | some d, .sat vs => .sat (vs.map fun (n, v) => (n, v.uncode d))
  | _, a => a

/-- Over-approximate, confirm, fall back: asks the abstract variant `abs` of the exact script whose datatypes and
variables are `dts` and `vars` and whose literals are `lits`; an unsat answer is the answer, as `Unsat` reads it. A sat
answer is confirmed by the exact script with the variant's model fixed (`confirmations`, keyed by `fixed`), whose sat
answer is the answer; where no fixing confirms it, or the variant has no verdict, the exact script answers (none: it
has no text). Every script asked is cached by its own text, and the answer comes with the key of the script that gave
it, whose kept answer it is with names read back (`Answer.uncode`). -/
def Solver.overApprox (s : Solver) (dir : System.FilePath) (ids : Option Nat) (dts : List Datatype) (vars : List Srt)
    (lits : List String) (abs : Keyed) (fixed : List Term → Option Keyed) (exact : IO (Option (Answer × String))) :
    IO (Option (Answer × String)) := do
  match ← s.runKeyed dir abs with
  | .unsat => return some (.unsat, abs.key)
  | .sat vs =>
    for fixes in confirmations dts vars lits vs do
      if let some q := fixed fixes then
        if let .sat ws ← s.runKeyed dir q then return some ((Answer.sat ws).uncode ids, q.key)
    exact
  | _ => exact

/-- Asks what the solver reads for a script (`Script.sent`, `ids` being the id datatype if the script has one): its
abstract variant first where it holds strings (`Solver.overApprox`), else the script; each answer read from the cache
directory `dir` where kept, with the key of the script that gave it (`Solver.overApprox`). An engine bug where a
script has no text (`noText`). -/
def Solver.runCached (s : Solver) (dir : System.FilePath) (ids : Option Nat) (script : Script) :
    IO (Except String (Answer × String)) := do
  let e := script.sent ids
  let exact : IO (Option (Answer × String)) := do
    let some q := e.keyed s.header | return none
    return some ((← s.runKeyed dir q).uncode ids, q.key)
  let fixed (fixes : List Term) : Option Keyed := { e with asserts := e.asserts ++ fixes }.keyed s.header
  let r ← match e.abs.bind (·.keyed s.header) with
    | none => exact
    | some a => s.overApprox dir ids e.datatypes e.vars e.lits a fixed exact
  return match r with
    | some a => .ok a
    | none => .error noText

/-- A question's direct key, as ccache's direct mode keys a result by a digest of the compiler, its options and the
source files instead of the preprocessed text, and Bazel keys an action by the digests of its command and inputs: the
SHA-256 of `inputs`, everything the engine reads to build the question's script, and of `name`, which of their
questions it is. -/
def directKey (inputs name : List String) : String := Sha256.hex (frame [frame inputs, frame name]).toUTF8

/-- The answer the direct key `direct` names in the cache directory `dir`, where the entry and its answer are kept. -/
def Solver.cached (dir : System.FilePath) (direct : String) (ids : Option Nat) : IO (Option Answer) := do
  let entry := dir / "direct" / direct
  if ← entry.pathExists then
    let answerFile := dir / ((← IO.FS.readFile entry) ++ ".answer")
    if ← answerFile.pathExists then
      return some ((Answer.parse (← IO.FS.readFile answerFile)).uncode ids)
  return none

/-- Asks a script as `Solver.runCached` does, first reading the answer its direct key `direct` (`directKey`) names in
the cache directory `dir`, without building the script: the key's entry holds the text key of the script whose answer
decided. That trusts the engine to build the same script from the same inputs, as it is deterministic. Where the entry
or its answer is missing (another spec, another engine), the script's text keys still find each answer kept, and the
entry is written for a decided answer (`Answer.decided`), as `Solver.runKeyed` keeps one. -/
def Solver.ask (s : Solver) (dir : System.FilePath) (direct : String) (ids : Option Nat) (script : Script) :
    IO (Except String Answer) := do
  if let some a ← Solver.cached dir direct ids then return .ok a
  let entry := dir / "direct" / direct
  match ← s.runCached dir ids script with
  | .error m => return .error m
  | .ok (a, key) =>
    if a.decided then
      IO.FS.createDirAll (dir / "direct")
      let partFile := entry.withExtension "part"
      IO.FS.writeFile partFile key
      IO.FS.rename partFile entry
    return .ok a

/-- A script's text parts with their shared definitions found, the definitions' sorts and the SHA-256 of the framed
parts: what scripts that add one goal assertion share (the goals of generate's targets and of a service's responses at
one depth). The assertions are to be merged into one object per equal subterm first (`shareCommon'`), with whatever
builds the goals, so finding a goal's shared terms among them stops at equal objects. -/
structure ScriptPrefix where
  script : Script
  defs : Defs
  sorts : Array Srt
  parts : TextParts
  digest : String

/-- The script `s` as the prefix of scripts that add a goal, read once; none as `Script.shared`. -/
def Script.prefix? (s : Script) (header : List String) : Option ScriptPrefix := do
  guard (Term.refFrees s.asserts)
  let (asserts, D) := Term.extracts s.asserts {}
  let sorts ← D.entries.foldlM (fun acc (_, b) => do pure (acc.push (← b.srt? s.datatypes s.vars acc))) #[]
  let parts := s.parts header asserts (D.entries.toList.map (·.2) |>.zip sorts.toList)
  pure ⟨s, D, sorts, parts, Sha256.hex (frame [parts.head, parts.body, parts.tail]).toUTF8⟩

/-- The prefix's script with `goals` as its last assertions, keyed: the text is the prefix's parts with the goals' new
definitions after the prefix's and their assertions after the prefix's, and the key is the SHA-256 of the prefix's
digest and those two pieces, so the key covers exactly what prints the text without printing the prefix again. None
as `Script.shared`. -/
def ScriptPrefix.askAll (p : ScriptPrefix) (goals : List Term) : Option Keyed := do
  guard (Term.refFrees goals)
  let (gs, D) := Term.extracts goals p.defs
  let fresh := D.entries.toList.drop p.defs.entries.size
  let sorts ← fresh.foldlM (fun acc (_, b) => do pure (acc.push (← b.srt? p.script.datatypes p.script.vars acc))) p.sorts
  let defs := linesText ((fresh.zip (sorts.toList.drop p.sorts.size)).zipIdx.map fun (((_, b), srt), i) =>
    defineLine (p.defs.entries.size + i) b srt)
  let asserts := linesText (gs.map fun g => s!"(assert {g.print})")
  pure ⟨Sha256.hex (frame [p.digest, defs, asserts]).toUTF8,
    fun _ => p.parts.head ++ defs ++ p.parts.body ++ asserts ++ p.parts.tail⟩

/-- The prefix's script with `goal` as its last assertion, keyed (`ScriptPrefix.askAll`). -/
def ScriptPrefix.ask (p : ScriptPrefix) (goal : Term) : Option Keyed := p.askAll [goal]

/-- The abstract variant (`Script.abs`) of a prefix's script, for scripts that add a goal to it: the variant's
prefix without the literals' order, which follows the goal as in `Script.abs`, the cache its terms were coded with, so
a goal's shared terms code to the prefix's objects, and the script's literals and variables. A goal with a literal the
prefix lacks has no variant here, as the literals' variables would differ. -/
structure AbsPrefix where
  pre : ScriptPrefix
  cache : SCodeCache
  lits : List String
  order : List Term

/-- The abstract variant's prefix of `s`, as `Script.abs` builds the variant of `s` with goals added. -/
def Script.absPrefix? (s : Script) (header : List String) : Option AbsPrefix := do
  guard s.funs.isEmpty
  let lits := s.lits
  guard (s.hasStrings lits)
  let base := s.vars.length
  let (ps, cache) := Term.scodesC s.datatypes s.vars (litVar lits base) s.asserts {}
  let ps ← ps
  guard (ps.all (·.2 == .bool))
  let vars := s.vars.map Srt.code ++ lits.map fun _ => Srt.int
  let pre ← Script.prefix? ⟨s.datatypes.map Datatype.code, vars, [2, 1], ps.map (·.1), List.range (base + lits.length)⟩
    header
  pure ⟨pre, cache, lits, litOrder lits base⟩

/-- What the solver reads for scripts that add a goal to one script (`Script.sent`): the prefix with names as codes
and the cache its terms were coded with, so a goal's shared terms code to the prefix's objects, where the script has
names as codes; the prefix as it is, read only for a goal that has no codes; and the abstract variant's prefix of
the prefix the goal is read with, asked first (`Solver.overApprox`). -/
structure SentPrefix where
  coded : Option (Nat × ScriptPrefix × CodeCache)
  exact : Thunk (Option ScriptPrefix)
  abs : Thunk (Option AbsPrefix)

/-- The prefix of what the solver reads for `s` and goals added to it, `ids` being the id datatype if any. -/
def Script.sentPrefix? (s : Script) (ids : Option Nat) (header : List String) : SentPrefix :=
  let coded := ids.bind fun d =>
    if s.datatypes[d]? == some idDatatype then
      match Term.codesC d s.asserts {} with
      | (some asserts, c) =>
        (Script.prefix? { s with datatypes := s.datatypes.set d codedIdDatatype, asserts } header).map (d, ·, c)
      | (none, _) => none
    else none
  let exact := Thunk.mk fun _ => s.prefix? header
  { coded, exact,
    abs := Thunk.mk fun _ => (match coded with | some (_, q, _) => some q | none => exact.get).bind
      (·.script.absPrefix? header) }

/-- What the solver reads exactly for the prefix's script with `goal` as its last assertion: with names as codes where
the goal has codes too, the prefix and the goal so; else the prefix as it is and the goal; and whether the prefix is
the one the abstract variant's prefix codes. -/
def SentPrefix.sent (p : SentPrefix) (goal : Term) : Option (ScriptPrefix × Term × Bool) :=
  match p.coded.bind fun (d, q, c) => ((goal.codeC d c).1).map (q, ·) with
  | some (q, g) => some (q, g, true)
  | none => p.exact.get.map (·, goal, p.coded.isNone)

/-- The abstract variant of what `sent` gives (`q` with `g`, `coded` whether the variant's prefix codes `q`), keyed;
none where the prefix has none or the goal's literals are not the prefix's. -/
def SentPrefix.absAsk (p : SentPrefix) (q : ScriptPrefix) (g : Term) (coded : Bool) : Option (AbsPrefix × Keyed) := do
  guard coded
  let a ← p.abs.get
  let (g', srt) ← (g.scodeC q.script.datatypes q.script.vars (litVar a.lits q.script.vars.length) a.cache).1
  guard (srt == .bool)
  pure (a, ← a.pre.askAll (g' :: a.order))

/-- Asks the solver about the prefix's script with `goal` as its last assertion: the abstract variant first where the
prefix has one and the goal's literals are the prefix's (`Solver.overApprox`), else what it reads exactly; each answer
read from the cache directory `dir` where kept. Without `fallback`, an abstract variant that decides nothing answers
unknown instead of asking the exact script: a cube that can still split is cheaper split. None where a script has no
text. -/
def Solver.askGoal (s : Solver) (dir : System.FilePath) (ids : Option Nat) (p : SentPrefix) (goal : Term)
    (fallback : Bool := true) : IO (Option Answer) := do
  let some (q, g, coded) := p.sent goal | return none
  let exact : IO (Option (Answer × String)) := do
    let some eq := q.ask g | return none
    return some ((← s.runKeyed dir eq).uncode ids, eq.key)
  let some (a, k) := p.absAsk q g coded | return (← exact).map (·.1)
  let r ← s.overApprox dir ids q.script.datatypes q.script.vars a.lits k (fun fixes => q.askAll (g :: fixes))
    (if fallback then exact else pure (some (.unknown "the abstract variant decided nothing", "")))
  return r.map (·.1)

/-- A question to the solver that owns its call: the script, the id datatype if it has one, and how its answer reads
as a result. Nothing pairs answers with questions by position. -/
structure Obligation (α : Type) where
  /-- Which question of its spec it is, unique among them: its direct key's part (`directKey`). -/
  name : List String
  script : Script
  ids : Option Nat
  read : Answer → α

end Tazuna.Smt
