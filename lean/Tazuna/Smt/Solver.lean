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

/-- Runs one script and reads the answer. -/
def Solver.run (s : Solver) (script : Script) : IO Answer := do
  let some text := script.text s.header | return .unknown "a shared term of the script has no sort"
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
    return .unknown s!"the solver ran past {s.timeoutMs} ms"
  let _ ← child.wait
  match out.get with
  | .ok text => return Answer.parse text
  | .error e => return .unknown s!"the solver's output did not read: {e}"

/-- A question to the solver that owns its call: the script, and how its answer reads as a result. Nothing pairs
answers with questions by position. -/
structure Obligation (α : Type) where
  script : Script
  read : Answer → α

def Obligation.run {α : Type} (s : Solver) (o : Obligation α) : IO α := do
  return o.read (← s.run o.script)

end Tazuna.Smt
