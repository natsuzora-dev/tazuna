import Tazuna.Smt.Script
import Tazuna.Smt.Sha256

/-! Running the solver. Each script runs in its own solver process, which reads the script from a file and prints its
answer on stdout; the process boundary contains a solver crash, and a run past its time is killed. This is the one
place that knows the solver is z3: its executable, its command line, and the header lines outside standard SMT-LIB,
its resource limit and its random seeds. -/

namespace Tazuna.Smt

structure Solver where
  path : String := "z3"
  /-- z3's deterministic resource limit, so the same script gets the same verdict on any machine. -/
  rlimit : Nat := 50000000
  /-- z3's random seeds, fixed so the same script gets the same answer, model included, on every run (Boogie sets
  the same two options). -/
  seed : Nat := 0
  /-- Wall-clock limit: the process is killed after this many ms. -/
  timeoutMs : Nat := 30000

/-- Beyond depth 5 z3 prints a value with `let` aliases, which values in SMT-LIB's model syntax do not have; the
depth limit is raised so every value prints as a term. -/
def Solver.header (s : Solver) : List String :=
  [s!"(set-option :rlimit {s.rlimit})", s!"(set-option :smt.random_seed {s.seed})",
    s!"(set-option :sat.random_seed {s.seed})", "(set-option :pp.max_depth 1000000)"]

/-- Runs one script's text: what the solver printed, or why it printed nothing to read. z3 reads a file about twice as
fast as the same text on stdin with `-in`, so the text goes to a temporary file. -/
def Solver.runText (s : Solver) (text : String) : IO (Except String String) :=
  IO.FS.withTempFile fun h path => do
    h.putStr text
    h.flush
    runFile path
where
  runFile (path : System.FilePath) : IO (Except String String) := do
    let child ← IO.Process.spawn
      { cmd := s.path, args := #["-smt2", path.toString], stdin := .null, stdout := .piped, stderr := .null }
    let out ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
    let deadline := (← IO.monoMsNow) + s.timeoutMs
    while !(← IO.hasFinished out) && (← IO.monoMsNow) < deadline do
      IO.sleep 5
    if !(← IO.hasFinished out) then
      child.kill
      let _ ← child.wait
      return .error s!"the solver ran past {s.timeoutMs} ms"
    let _ ← child.wait
    match out.get with
    | .ok text => return .ok text
    | .error e => return .error s!"the solver's output did not read: {e}"

/-- What the solver says its version is: the cache keeps each version's answers apart. -/
def Solver.version (s : Solver) : IO String := do
  let out ← IO.Process.output { cmd := s.path, args := #["-version"] }
  return out.stdout.trimAscii.toString

/-- Runs one script and reads the answer. -/
def Solver.run (s : Solver) (script : Script) : IO Answer := do
  let some text := script.text s.header | return .unknown "a shared term of the script has no sort"
  match ← s.runText text with
  | .ok out => return Answer.parse out
  | .error why => return .unknown why

/-- Runs one script, or reads its answer from the cache directory `dir`: a sat or unsat answer is kept under the
SHA-256 of the script's text, as ccache and Bazel key results by a digest of their inputs, so the cache keeps no
script. The text holds the solver's header (resource limit, seeds), so the same text gets the same answer; an unknown
answer, which a wall-clock limit may give, is not kept. -/
def Solver.runCached (s : Solver) (dir : System.FilePath) (script : Script) : IO Answer := do
  let some text := script.text s.header | return .unknown "a shared term of the script has no sort"
  let answerFile := dir / (Sha256.hex text.toUTF8 ++ ".answer")
  if ← answerFile.pathExists then
    return Answer.parse (← IO.FS.readFile answerFile)
  match ← s.runText text with
  | .error why => return .unknown why
  | .ok out =>
    let a := Answer.parse out
    match a with
    | .unknown _ => pure ()
    | _ =>
      IO.FS.createDirAll dir
      -- A run stopped mid-write leaves no answer file to misread.
      let partFile := answerFile.withExtension "part"
      IO.FS.writeFile partFile out
      IO.FS.rename partFile answerFile
    return a

/-- A question to the solver that owns its call: the script, and how its answer reads as a result. Nothing pairs
answers with questions by position. -/
structure Obligation (α : Type) where
  script : Script
  read : Answer → α

def Obligation.run {α : Type} (s : Solver) (o : Obligation α) : IO α := do
  return o.read (← s.run o.script)

end Tazuna.Smt
