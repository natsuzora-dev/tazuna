import Lean.Data.Json

/-! The IR as the converter writes it: Gleam's syntax with names resolved and every node annotated with its type. It
keeps the surface constructs (pipe, `use`, shorthand labels, let patterns, alternative patterns) and literals as
source text; Lean gives them meaning in `Tazuna.Ir.Elab`.

The JSON contract, version 2:

- Program: `{"tazuna_ir": 2, "root", "sources": [{"module", "path"}], "types", "functions", "constants"}`. A global's
  name is `module.name`; its module's source path locates its errors.
- Type: `{"con": name, "args": [..]}`, `{"fn": [..], "ret"}`, `{"tuple": [..]}`, `{"var": name}`, and in source
  annotations only `{"hole": text}`.
- Declarations: types `{"name", "params", "variants": [{"name", "fields": [{"label"?, "ty"}]}], "at"}`; functions
  `{"name", "params": [{"label"?, "name", "ty"}], "ret", "body", "at"}`; constants `{"name", "ty", "value", "at"}`.
- Every expression and pattern carries `"ty"` and `"at": [line, column]`. Operators (`"bin"`, `"un"`) name Gleam's symbol
  in `"operator"`.
- Arguments of calls, constructors, record updates and constructor patterns are `{"label"?, "value"?}` (patterns:
  `"pattern"?`) in source order. A labelled argument without a value is shorthand for the variable named by the label;
  it carries its own `"at"`. A positional argument's place is its value's `"at"`. -/

namespace Tazuna.Ir.Surface

open Lean (Json)

structure At where
  line : Nat
  col : Nat
deriving Inhabited, BEq, Repr

def At.lt (a b : At) : Bool := a.line < b.line || (a.line == b.line && a.col < b.col)

inductive STy where
  | con (name : String) (args : List STy)
  | fn (ps : List STy) (r : STy)
  | tuple (ts : List STy)
  | var (name : String)
  | hole (text : String)
deriving Inhabited

mutual
inductive Pat where
  | mk (pos : At) (ty : STy) (node : PatNode)
inductive PatNode where
  | discard (name : String)
  | var (name : String)
  | int (text : String)
  | str (text : String)
  | tuple (items : List Pat)
  | ctor (type variant : String) (args : List PatArg) (spread : Bool)
  | as (pattern : Pat) (name : String)
inductive PatArg where
  | mk (pos : At) (label : Option String) (pattern : Option Pat)
end

instance : Inhabited Pat := ⟨.mk ⟨0, 0⟩ (.hole "_") (.discard "_")⟩

mutual
inductive Expr where
  | mk (pos : At) (ty : STy) (node : Node)
inductive Node where
  | int (text : String)
  | str (text : String)
  | var (name : String)
  | ref (name : String) (targs : List (String × STy))
  | ctor (type variant : String) (args : List Arg)
  | field (record : Expr) (label : String)
  | index (tuple : Expr) (k : Nat)
  | update (type variant : String) (record : Expr) (fields : List Arg)
  | call (fn : Expr) (args : List Arg)
  | pipe (left right : Expr)
  | lam (params : List Param) (ret : Option STy) (body : Expr)
  | block (stmts : List Stmt)
  | case (subjects : List Expr) (clauses : List Clause)
  | list (items : List Expr)
  | tuple (items : List Expr)
  | bin (op : String) (left right : Expr)
  | un (op : String) (arg : Expr)
inductive Arg where
  | mk (pos : At) (label : Option String) (value : Option Expr)
inductive Param where
  | mk (name : String) (ty : STy) (annotation : Option STy)
inductive Stmt where
  | let_ (pos : At) (pattern : Pat) (annotation : Option STy) (value : Expr)
  | use (pos : At) (patterns : List Pat) (call : Expr)
  | expr (value : Expr)
inductive Clause where
  | mk (alternatives : List (List Pat)) (guard : Option Expr) (body : Expr)
end

instance : Inhabited Expr := ⟨.mk ⟨0, 0⟩ (.hole "_") (.int "0")⟩

def Expr.pos : Expr → At | .mk a _ _ => a

structure TypeDef where
  name : String
  params : List String
  variants : List (String × List (Option String × STy))
  pos : At

structure FunDef where
  name : String
  params : List (Option String × String × STy)
  ret : STy
  body : Expr
  pos : At

structure ConstDef where
  name : String
  ty : STy
  value : Expr
  pos : At

structure Program where
  version : Nat
  root : String
  sources : List (String × String)
  types : List TypeDef
  functions : List FunDef
  constants : List ConstDef

/-- A JSON reading error, with the position of the innermost node read so far. -/
abbrev R := ExceptT String (StateM (Option At))

def get (j : Json) (k : String) : R Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing \"{k}\" in {j.compress.take 120}"

def opt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null | .error _ => none
  | .ok v => some v

def str (j : Json) (k : String) : R String := do
  match (← get j k).getStr? with | .ok s => pure s | .error e => throw s!"\"{k}\": {e}"

def optStr (j : Json) (k : String) : R (Option String) :=
  match opt j k with
  | none => pure none
  | some v => match v.getStr? with | .ok s => pure (some s) | .error e => throw s!"\"{k}\": {e}"

def nat (j : Json) (k : String) : R Nat := do
  match (← get j k).getNat? with | .ok n => pure n | .error e => throw s!"\"{k}\": {e}"

def arr (j : Json) (k : String) : R (List Json) := do
  match (← get j k).getArr? with | .ok a => pure a.toList | .error e => throw s!"\"{k}\": {e}"

def readAt (j : Json) : R At := do
  match ← arr j "at" with
  | [l, c] => match l.getNat?, c.getNat? with
    | .ok l, .ok c => let a := ⟨l, c⟩; set (some a); pure a
    | _, _ => throw "\"at\" must be [line, column]"
  | _ => throw "\"at\" must be [line, column]"

partial def readTy (j : Json) : R STy := do
  if let some n := opt j "con" then
    let .ok n := n.getStr? | throw "\"con\" must be a string"
    return .con n (← (← arr j "args").mapM readTy)
  if let some ps := opt j "fn" then
    let .ok ps := ps.getArr? | throw "\"fn\" must be an array"
    return .fn (← ps.toList.mapM readTy) (← readTy (← get j "ret"))
  if let some ts := opt j "tuple" then
    let .ok ts := ts.getArr? | throw "\"tuple\" must be an array"
    return .tuple (← ts.toList.mapM readTy)
  if let some n := opt j "var" then
    let .ok n := n.getStr? | throw "\"var\" must be a string"
    return .var n
  if let some n := opt j "hole" then
    let .ok n := n.getStr? | throw "\"hole\" must be a string"
    return .hole n
  throw s!"not a type: {j.compress.take 120}"

def optTy (j : Json) (k : String) : R (Option STy) :=
  match opt j k with | none => pure none | some t => some <$> readTy t

partial def readPat (j : Json) : R Pat := do
  let pos ← readAt j
  let ty ← readTy (← get j "ty")
  let node ← match ← str j "p" with
    | "discard" => pure (.discard (← str j "name"))
    | "var" => pure (.var (← str j "name"))
    | "int" => pure (.int (← str j "text"))
    | "str" => pure (.str (← str j "text"))
    | "tuple" => pure (.tuple (← (← arr j "items").mapM readPat))
    | "ctor" =>
      let args ← (← arr j "args").mapM fun a => do
        let label ← optStr a "label"
        match opt a "pattern" with
        | some p => let p ← readPat p; pure (PatArg.mk (match p with | .mk pos .. => pos) label (some p))
        | none => pure (PatArg.mk (← readAt a) label none)
      let spread ← match opt j "spread" with
        | none => pure false
        | some b => match b.getBool? with | .ok b => pure b | .error _ => throw "\"spread\" must be a boolean"
      pure (.ctor (← str j "type") (← str j "variant") args spread)
    | "as" => pure (.as (← readPat (← get j "pattern")) (← str j "name"))
    | p => throw s!"unknown pattern \"{p}\""
  return .mk pos ty node

mutual
partial def readArg (j : Json) : R Arg := do
  let label ← optStr j "label"
  match opt j "value" with
  | some v => let v ← readExpr v; pure (.mk v.pos label (some v))
  | none => pure (.mk (← readAt j) label none)

partial def readStmt (j : Json) : R Stmt := do
  match ← str j "stmt" with
  | "let" => pure (.let_ (← readAt j) (← readPat (← get j "pattern")) (← optTy j "annotation")
      (← readExpr (← get j "value")))
  | "use" => pure (.use (← readAt j) (← (← arr j "patterns").mapM readPat) (← readExpr (← get j "call")))
  | "expr" => pure (.expr (← readExpr (← get j "value")))
  | s => throw s!"unknown statement \"{s}\""

partial def readExpr (j : Json) : R Expr := do
  let pos ← readAt j
  let ty ← readTy (← get j "ty")
  let sub (k : String) : R Expr := do readExpr (← get j k)
  let subs (k : String) : R (List Expr) := do (← arr j k).mapM readExpr
  let node ← match ← str j "op" with
    | "int" => pure (.int (← str j "text"))
    | "str" => pure (.str (← str j "text"))
    | "var" => pure (.var (← str j "name"))
    | "ref" =>
      let targs ← match ← get j "targs" with
        | .obj kvs => kvs.toList.mapM fun (k, v) => do return (k, ← readTy v)
        | _ => throw "\"targs\" must be an object"
      pure (.ref (← str j "name") targs)
    | "ctor" => pure (.ctor (← str j "type") (← str j "variant") (← (← arr j "args").mapM readArg))
    | "field" => pure (.field (← sub "record") (← str j "label"))
    | "index" => pure (.index (← sub "tuple") (← nat j "index"))
    | "update" => pure (.update (← str j "type") (← str j "variant") (← sub "record")
        (← (← arr j "fields").mapM readArg))
    | "call" => pure (.call (← sub "fn") (← (← arr j "args").mapM readArg))
    | "pipe" => pure (.pipe (← sub "left") (← sub "right"))
    | "lam" =>
      let ps ← (← arr j "params").mapM fun p => do
        return Param.mk (← str p "name") (← readTy (← get p "ty")) (← optTy p "annotation")
      pure (.lam ps (← optTy j "return_annotation") (← sub "body"))
    | "block" => pure (.block (← (← arr j "stmts").mapM readStmt))
    | "case" =>
      let clauses ← (← arr j "clauses").mapM fun c => do
        let alts ← (← arr c "alternatives").mapM fun a => do
          let .ok ps := a.getArr? | throw "an alternative must be an array of patterns"
          ps.toList.mapM readPat
        let guard ← match opt c "guard" with | none => pure none | some g => some <$> readExpr g
        return Clause.mk alts guard (← readExpr (← get c "body"))
      pure (.case (← subs "subjects") clauses)
    | "list" => pure (.list (← subs "items"))
    | "tuple" => pure (.tuple (← subs "items"))
    | "bin" => pure (.bin (← str j "operator") (← sub "left") (← sub "right"))
    | "un" => pure (.un (← str j "operator") (← sub "arg"))
    | op => throw s!"unknown expression \"{op}\""
  return .mk pos ty node
end

/-- A failure to read a declaration names it, so its module's source locates the error. -/
structure ReadError where
  global : Option String
  pos : Option At
  message : String

def inGlobal {α} (name : String) (r : R α) : ExceptT ReadError Id α :=
  match (r.run.run none) with
  | (.ok a, _) => pure a
  | (.error e, pos) => throw ⟨some name, pos, e⟩

def topLevel {α} (r : R α) : ExceptT ReadError Id α :=
  match (r.run.run none) with
  | (.ok a, _) => pure a
  | (.error e, pos) => throw ⟨none, pos, e⟩

def readProgram (j : Json) : Except ReadError Program := do
  let version ← topLevel (nat j "tazuna_ir")
  let root ← topLevel (str j "root")
  let sources ← topLevel do (← arr j "sources").mapM fun s => do return (← str s "module", ← str s "path")
  let types ← (← topLevel (arr j "types")).mapM fun t => do
    let name ← topLevel (str t "name")
    inGlobal name do
      let variants ← (← arr t "variants").mapM fun v => do
        return (← str v "name", ← (← arr v "fields").mapM fun f => do return (← optStr f "label", ← readTy (← get f "ty")))
      let params ← (← arr t "params").mapM fun p => match p.getStr? with
        | .ok s => pure s | .error _ => throw "a type parameter must be a string"
      return { name, params, variants, pos := ← readAt t : TypeDef }
  let functions ← (← topLevel (arr j "functions")).mapM fun f => do
    let name ← topLevel (str f "name")
    inGlobal name do
      let pos ← readAt f
      let params ← (← arr f "params").mapM fun p => do
        return (← optStr p "label", ← str p "name", ← readTy (← get p "ty"))
      return { name, params, ret := ← readTy (← get f "ret"), body := ← readExpr (← get f "body"), pos : FunDef }
  let constants ← (← topLevel (arr j "constants")).mapM fun c => do
    let name ← topLevel (str c "name")
    inGlobal name do
      let pos ← readAt c
      return { name, ty := ← readTy (← get c "ty"), value := ← readExpr (← get c "value"), pos : ConstDef }
  return { version, root, sources, types, functions, constants }

end Tazuna.Ir.Surface
