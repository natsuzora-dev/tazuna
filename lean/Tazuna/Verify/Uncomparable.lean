import Tazuna.Data.Group
import Tazuna.Syntax.Structure

namespace Tazuna.Verify

open Tazuna.Data

/--
A line or file that verify cannot compare. `line` is 1-based in the violation's file, and `snapshotLine` is
1-based in the snapshot. `searchLimit` is at the `in` lines before the window (1 for the first window), or at
the compared `in` lines, whose comparison takes more steps than verify searches.
-/
inductive Uncomparable where
  | lineSchema (line : Nat)
  | unknownRequest (line : Nat) (type name : String)
  | unknownAnswer (line : Nat) (to : String)
  | unknownEvent (line : Nat) (event : String)
  | resultOfUnknownRequest (line : Nat) (event : Syntax.Ref) (requestId : String)
  | resultOfNonCommand (line : Nat) (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | unknownAfter (line : Nat) (id : String)
  | unexpectedInput (line : Nat) (input : Value)
  | missingInput (line : Nat) (input : Value) (snapshotLine : Nat)
  | answersNoRequest (line : Nat) (to : String) (snapshotLine : Nat)
  | differentInput (line snapshotLine : Nat) (snapshot trace : Value)
  | searchLimit (line snapshotLine : Nat)
  | unknownService (service : String)
  | unknownScenario (scenario : Syntax.Ref)
  | missingTrace (definition : Syntax.Ref)
  | unknownTraceEntry
  | missingSnapshot (definition : Syntax.Ref)
  | obsoleteSnapshot
  | unknownSnapshotEntry

derive_group Uncomparable

end Tazuna.Verify
