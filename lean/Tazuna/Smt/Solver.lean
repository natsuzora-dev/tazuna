import Tazuna.Smt.NameCode
import Tazuna.Smt.Sha256

/-! Running the solver. Each script runs in its own solver process, which reads the script from a file and prints its
answer on stdout; the process boundary contains a solver crash, and a run past its time is killed. This is the one
place that knows the solver is z3: its executable, its command line, and the header lines outside standard SMT-LIB,
its resource limit and its random seeds. -/

namespace Tazuna.Smt

structure Solver where
  path : String
  /-- z3's deterministic resource limit, so the same script gets the same verdict on any machine. About 6 s of z3 on a
  laptop; the largest question of the 3-service benchmark takes a third of it. -/
  rlimit : Nat := 50000000
  /-- z3's random seeds, fixed so the same script gets the same answer, model included, on every run (Boogie sets
  the same two options). -/
  seed : Nat := 0
  /-- The wall-clock safety net: the process is killed after this many ms, a hundred times what the resource limit
  takes on a laptop, so the resource limit stops z3 first on any machine that runs it. -/
  timeoutMs : Nat := 600000

/-- z3 beside the engine's executable, where the launcher puts the z3 it fetched with the engine; else z3 on PATH, as
for an engine built from lean/ that `TAZUNA_ENGINE` names. -/
def Solver.find : IO Solver := do
  let beside := (← IO.appDir) / (if System.Platform.isWindows then "z3.exe" else "z3")
  return { path := if ← beside.pathExists then beside.toString else "z3" }

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
    let child ← IO.Process.spawn
      { cmd := s.path, args := #["-smt2", path.toString], stdin := .null, stdout := .piped, stderr := .null }
    let out ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
    let deadline := (← IO.monoMsNow) + s.timeoutMs
    while !(← IO.hasFinished out) && (← IO.monoMsNow) < deadline do
      IO.sleep 5
    if !(← IO.hasFinished out) then
      child.kill
      let _ ← child.wait
      return .error (.timeout s.timeoutMs)
    let _ ← child.wait
    match out.get with
    | .ok text => return .ok text
    | .error e => return .error (.unknown s!"the solver's output did not read: {e}")

/-- What the solver says its version is: the cache keeps each version's answers apart. -/
def Solver.version (s : Solver) : IO String := do
  let out ← IO.Process.output { cmd := s.path, args := #["-version"] }
  return out.stdout.trimAscii.toString

-- A script's answer reports every variable it declares, so the default is never read.
set_option linter.tazuna.silentDefault false in
/-- The values the solver gave, as a model. -/
def modelOf (vs : List (Nat × Val)) : Model :=
  { vars := fun n => (vs.lookup n).getD default, divZero := fun _ => 0, modZero := fun _ => 0,
    selOther := fun _ _ _ _ => default, defs := fun _ => default }

/-- Why a script has no text: a shared term without a sort. The encoder builds only sorted terms, but no theorem
states it, so where it happens it is an engine bug, never a spec's undecided line. -/
def noSort : String := "a shared term of the script has no sort; the encoder builds only sorted terms (unproved)"

/-- Runs one script and reads the answer; smt-check's runner, which reads a script without text as unknown. -/
def Solver.run (s : Solver) (script : Script) : IO Answer := do
  let some text := script.text s.header | return .unknown noSort
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

/-- Runs what the solver reads for a script (`Script.sent`, `ids` being the id datatype if the script has one), or
reads its answer from the cache directory `dir`, keyed by its whole text; an engine bug where the script has no text
(`noSort`). -/
def Solver.runCached (s : Solver) (dir : System.FilePath) (ids : Option Nat) (script : Script) :
    IO (Except String Answer) := do
  let some q := (script.sent ids).keyed s.header | return .error noSort
  return .ok ((← s.runKeyed dir q).uncode ids)

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

/-- The script `s` as the prefix of scripts that add a goal, read once. -/
def Script.prefix? (s : Script) (header : List String) : Option ScriptPrefix := do
  let (asserts, D) := Term.extracts s.asserts {}
  let sorts ← D.entries.foldlM (fun acc (_, b) => do pure (acc.push (← b.srt? s.datatypes s.vars acc))) #[]
  let parts := s.parts header asserts (D.entries.toList.map (·.2) |>.zip sorts.toList)
  pure ⟨s, D, sorts, parts, Sha256.hex (frame [parts.head, parts.body, parts.tail]).toUTF8⟩

/-- The prefix's script with `goal` as its last assertion, keyed: the text is the prefix's parts with the goal's new
definitions after the prefix's and its assertion after the prefix's, and the key is the SHA-256 of the prefix's digest
and those two pieces, so the key covers exactly what prints the text without printing the prefix again. None where a
new definition has no sort. -/
def ScriptPrefix.ask (p : ScriptPrefix) (goal : Term) : Option Keyed := do
  let (g, D) := goal.extract p.defs
  let fresh := D.entries.toList.drop p.defs.entries.size
  let sorts ← fresh.foldlM (fun acc (_, b) => do pure (acc.push (← b.srt? p.script.datatypes p.script.vars acc))) p.sorts
  let defs := linesText ((fresh.zip (sorts.toList.drop p.sorts.size)).zipIdx.map fun (((_, b), srt), i) =>
    defineLine (p.defs.entries.size + i) b srt)
  let assert := linesText [s!"(assert {g.print})"]
  pure ⟨Sha256.hex (frame [p.digest, defs, assert]).toUTF8,
    fun _ => p.parts.head ++ defs ++ p.parts.body ++ assert ++ p.parts.tail⟩

/-- What the solver reads for scripts that add a goal to one script (`Script.sent`): the prefix with names as codes
and the cache its terms were coded with, so a goal's shared terms code to the prefix's objects, where the script has
names as codes; and the prefix as it is, read only for a goal that has no codes. -/
structure SentPrefix where
  coded : Option (Nat × ScriptPrefix × CodeCache)
  exact : Thunk (Option ScriptPrefix)

/-- The prefix of what the solver reads for `s` and goals added to it, `ids` being the id datatype if any. -/
def Script.sentPrefix? (s : Script) (ids : Option Nat) (header : List String) : SentPrefix :=
  let coded := ids.bind fun d =>
    if s.datatypes[d]? == some idDatatype then
      match Term.codesC d s.asserts {} with
      | (some asserts, c) =>
        (Script.prefix? { s with datatypes := s.datatypes.set d codedIdDatatype, asserts } header).map (d, ·, c)
      | (none, _) => none
    else none
  { coded, exact := Thunk.mk fun _ => s.prefix? header }

/-- What the solver reads for the prefix's script with `goal` as its last assertion, keyed: with names as codes where
the goal has codes too, else as it is. -/
def SentPrefix.ask (p : SentPrefix) (goal : Term) : Option Keyed :=
  match p.coded.bind fun (d, q, c) => ((goal.codeC d c).1).map (q, ·) with
  | some (q, g) => q.ask g
  | none => p.exact.get.bind (·.ask goal)

/-- A question to the solver that owns its call: the script, the id datatype if it has one, and how its answer reads
as a result. Nothing pairs answers with questions by position. -/
structure Obligation (α : Type) where
  script : Script
  ids : Option Nat
  read : Answer → α

end Tazuna.Smt
