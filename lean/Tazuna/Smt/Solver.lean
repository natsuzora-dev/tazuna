import Tazuna.Smt.Script

/-! Running the solver. Each script runs in its own solver process, which reads the script on stdin and prints its
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

/-- Runs one script's text: what the solver printed, or why it printed nothing to read. -/
def Solver.runText (s : Solver) (text : String) : IO (Except String String) := do
  let child ← IO.Process.spawn
    { cmd := s.path, args := #["-in", "-smt2"], stdin := .piped, stdout := .piped, stderr := .null }
  let (stdin, child) ← child.takeStdin
  stdin.putStr text
  stdin.flush
  -- Dropping the handle closes the solver's stdin, so it reads to the end.
  let _ := stdin
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

/-- Runs one script, or reads its answer from the cache directory `dir`: a sat or unsat answer is kept under the hash
of the script's text, beside that text. A hit compares the whole text, so two scripts whose hashes collide never
share an answer. The text holds the solver's header (resource limit, seeds), so the same text gets the same answer;
an unknown answer, which a wall-clock limit may give, is not kept. -/
def Solver.runCached (s : Solver) (dir : System.FilePath) (script : Script) : IO Answer := do
  let some text := script.text s.header | return .unknown "a shared term of the script has no sort"
  let key := s!"{hash text}"
  let scriptFile := dir / (key ++ ".smt2")
  let answerFile := dir / (key ++ ".answer")
  if ← answerFile.pathExists then
    if (← IO.FS.readFile scriptFile) == text then
      return Answer.parse (← IO.FS.readFile answerFile)
  match ← s.runText text with
  | .error why => return .unknown why
  | .ok out =>
    let a := Answer.parse out
    match a with
    | .unknown _ => pure ()
    | _ =>
      IO.FS.createDirAll dir
      IO.FS.writeFile scriptFile text
      -- A run stopped mid-write leaves no answer file to misread.
      let partFile := dir / (key ++ ".part")
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
