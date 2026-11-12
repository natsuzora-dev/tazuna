import Tazuna.Syntax.Structure
import Tazuna.Verify.Compare

/-! This module prepares trace lines for comparison. The `ask` parameter reads a value by its schema. -/

namespace Tazuna.Verify

open Tazuna.Data
open Tazuna.Syntax

/-- Where the schema comes from: a definition's input, output or payload, or a screen control's payload. -/
inductive Part where
  | input
  | output
  | payload
  | control (name : String)

/-- The value read by the definition's schema when the definition is known, and as a plain CValue otherwise. -/
def readValue {m : Type → Type} [Monad m] (ask : Definition → Part → Value → m CValue) (d : Option Definition)
    (part : Part) (v : Value) : m CValue :=
  match d with
  | some d => ask d part v
  | none => pure (CValue.ofValue v)

def comparableAnswer {m : Type → Type} [Monad m] (ask : Definition → Part → Value → m CValue)
    (shape : Option Definition) : Answer → m (Answer × Option CValue)
  | .rejected r => pure (.rejected { kind := r.kind }, none)
  | .accepted none => pure (.accepted none, none)
  | .accepted (some output) => do
    let compared ← readValue ask shape .output output
    pure (.accepted (some compared.flatten), some compared)
  | .fulfilled output => do
    let compared ← readValue ask shape .output output
    pure (.fulfilled compared.flatten, some compared)

/--
The comparable form of a trace line. An answer's output is read with the output schema of the definition that its
request line named. `outputByRequestId` carries over from the snapshot lines to the implementation lines.
-/
def canonicalLine {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue)
    (outputByRequestId : List (String × Definition)) (l : TraceLine) : m (Line × List (String × Definition)) := do
  let read := readValue ask
  let line (body : TraceLine.Body) (value : Option CValue) : Line := { l with body, value }
  let request (d : Option Definition) (id : Option String) : List (String × Definition) :=
    match d, id with
    | some d, some id => if d.hasOutput then setAt outputByRequestId id d else outputByRequestId
    | _, _ => outputByRequestId
  let control (name : String) : Option Definition × Part :=
    let (screen, control) := match name.splitOn "." with
      | first :: second :: _ => (first, second)
      | parts => (parts.headD "", "")
    let d := s.named service (some screen) ["screen"]
    let hasPayload := (d.bind fun d => d.chart?.bind fun c => c.controls.lookup control).any (·.isSome)
    (if hasPayload then d else none, .control control)
  match l.body with
  | .operation dir id name payload =>
    let (d, part) := control name
    let value ← payload.mapM (read d part)
    pure (line (.operation dir id name (value.map (·.flatten))) value, outputByRequestId)
  | .unacceptedOperation dir id name payload =>
    let (d, part) := control name
    let value ← payload.mapM (read d part)
    pure (line (.unacceptedOperation dir id name (value.map (·.flatten))) value, outputByRequestId)
  | .answer dir id to answer =>
    let (answer, value) ← comparableAnswer ask (outputByRequestId.lookup to) answer
    pure (line (.answer dir id to answer) value, outputByRequestId)
  | .event dir id name payload resultOf =>
    let value ← read (s.named service (some name) ["event"]) .payload payload
    pure (line (.event dir id name value.flatten resultOf) (some value), outputByRequestId)
  | .command dir id name input =>
    let d := s.named service (some name) ["command"]
    let value ← read d .input input
    pure (line (.command dir id name value.flatten) (some value), request d id)
  | .query dir id name input =>
    let d := s.named service (some name) ["query"]
    let value ← read d .input input
    pure (line (.query dir id name value.flatten) (some value), request d id)
  | .subscribe dir id name input =>
    let d := s.named service (some name) ["query"]
    let value ← read d .input input
    pure (line (.subscribe dir id name value.flatten) (some value), request d id)
  | .unsubscribe .. | .time .. | .restart .. => pure (line l.body none, outputByRequestId)

def canonicalLines {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue) :
    List (Option TraceLine) → List (String × Definition) → m (List (Option Line) × List (String × Definition))
  | [], outputByRequestId => pure ([], outputByRequestId)
  | none :: ls, outputByRequestId => do
    let (rest, outputByRequestId) ← canonicalLines s service ask ls outputByRequestId
    pure (none :: rest, outputByRequestId)
  | some l :: ls, outputByRequestId => do
    let (line, outputByRequestId) ← canonicalLine s service ask outputByRequestId l
    let (rest, outputByRequestId) ← canonicalLines s service ask ls outputByRequestId
    pure (some line :: rest, outputByRequestId)

/--
The lines with each `out` answer to a subscription that equals the previous answer to it set to `none`. A
subscription is open from the `in` subscribe to the `in` unsubscribe. Values compare ignoring bag order and object
field order.
-/
def withoutRepeatedAnswers (lines : List (Option Line)) : List (Option Line) :=
  go lines []
where
  go : List (Option Line) → List (String × Option String) → List (Option Line)
    | [], _ => []
    | none :: ls, o => none :: go ls o
    | some l :: ls, o =>
      match l.body with
      | .subscribe .in (some id) _ _ => some l :: go ls (if (o.lookup id).isSome then o else o ++ [(id, none)])
      | .unsubscribe .in _ to => some l :: go ls (o.filter (·.1 != to))
      | .answer .out _ to answer =>
        match o.lookup to with
        | some last =>
          let k := (answerContent answer l.value).key
          if last == some k then none :: go ls o else some l :: go ls (setAt o to (some k))
        | none => some l :: go ls o
      | _ => some l :: go ls o

/-- Whether `l` is an `out` event line whose definition exists and no contract lists. -/
def internalEvent (s : Structure) (service : String) (l : Line) : Bool :=
  match l.body with
  | .event .out _ name _ _ =>
    match s.named service (some name) ["event"] with
    | some d => (s.contractsListing d.ref).isEmpty
    | none => false
  | _ => false

def verifyLines {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue)
    (snapshot : List (Option TraceLine)) (trace : List (FileLine TraceLine)) : m Compared := do
  let (lines, malformed) := untilMalformed trace
  let (expected, outputByRequestId) ← canonicalLines s service ask snapshot []
  let (actual, _) ← canonicalLines s service ask lines outputByRequestId
  pure (compare expected (withoutRepeatedAnswers actual) malformed (internalEvent s service))

end Tazuna.Verify
