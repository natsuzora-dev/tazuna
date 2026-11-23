import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Tazuna.Semantics.Explore.Instrument
import Tazuna.Semantics.Validation.Check
import Tazuna.Semantics.Verify.External
import Tazuna.Semantics.Verify.Pairing
import Tazuna.Semantics.Verify.Snapshot

/-!
Lean.Json objects sort fields by name (Std.TreeMap), so this module parses and renders `Ir.Value`, which keeps the
field order that TS writes.
-/

namespace Tazuna.Json

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Explore
open Std.Internal.Parsec Std.Internal.Parsec.String

mutual

partial def arrayCore (acc : Array Value) : Parser (Array Value) := do
  let acc := acc.push (← anyCore)
  let c ← any
  if c == ']' then ws; pure acc
  else if c == ',' then ws; arrayCore acc
  else fail "unexpected character in array"

partial def objectCore (acc : Array (String × Value)) : Parser (Array (String × Value)) := do
  skipChar '"'
  let k ← Lean.Json.Parser.str
  ws; skipChar ':'; ws
  let acc := acc.push (k, ← anyCore)
  let c ← any
  if c == '}' then ws; pure acc
  else if c == ',' then ws; objectCore acc
  else fail "unexpected character in object"

partial def anyCore : Parser Value := do
  let c ← peek!
  if c == '[' then
    skip; ws
    if (← peek!) == ']' then skip; ws; pure (.arr [])
    else pure (.arr (← arrayCore #[]).toList)
  else if c == '{' then
    skip; ws
    if (← peek!) == '}' then skip; ws; pure (.obj [])
    else pure (.obj (← objectCore #[]).toList)
  else if c == '"' then
    skip
    let s ← Lean.Json.Parser.str
    ws; pure (.str s)
  else if c == 'f' then skipString "false"; ws; pure (.bool false)
  else if c == 't' then skipString "true"; ws; pure (.bool true)
  else if c == 'n' then skipString "null"; ws; pure .null
  else if c == '-' || ('0' ≤ c && c ≤ '9') then
    let n ← Lean.Json.Parser.num
    ws; pure (.num n)
  else fail "unexpected input"

end

def parse (text : String) : Except String Value :=
  Parser.run (do ws; let v ← anyCore; eof; pure v) text

partial def render : Value → String
  | .null => "null"
  | .bool b => toString b
  | .num n => toString n
  | .str s => Lean.Json.renderString s
  | .arr vs => "[" ++ ",".intercalate (vs.map render) ++ "]"
  | .obj fs => "{" ++ ",".intercalate (fs.map fun (k, v) => Lean.Json.renderString k ++ ":" ++ render v) ++ "}"

def asList : Value → Except String (List Value)
  | .arr vs => pure vs
  | v => throw s!"expected an array, got {render v}"

end Tazuna.Json
