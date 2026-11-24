import Lean.Data.Json.Elab
import Tazuna.Ir.Load

/-! Hand-made IRs: one well-typed program that uses every surface construct, and one refusal per kind of converter
bug the loader must catch. Each fixture's types are chosen so that a wrong desugaring or placement would be ill-typed. -/

namespace Tazuna.Ir.Examples

open Lean (Json)

def I : Json := json% {"con": "Int", "args": []}
def S : Json := json% {"con": "String", "args": []}
def B : Json := json% {"con": "Bool", "args": []}
def named (n : String) : Json := json% {"con": $(n), "args": []}
def fnT (ps : List Json) (r : Json) : Json := json% {"fn": $(Json.arr ps.toArray), "ret": $(r)}
def tupT (ts : List Json) : Json := json% {"tuple": $(Json.arr ts.toArray)}
def varT (n : String) : Json := json% {"var": $(n)}
def pos (l c : Nat) : Json := json% [$(l), $(c)]
def arr (xs : List Json) : Json := .arr xs.toArray

def node (op : String) (ty : Json) (l c : Nat) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("op", Json.str op), ("ty", ty), ("at", pos l c)] ++ fields)
def int (l c : Nat) (text : String) : Json := node "int" I l c [("text", text)]
def str (l c : Nat) (text : String) : Json := node "str" S l c [("text", text)]
def var (l c : Nat) (ty : Json) (n : String) : Json := node "var" ty l c [("name", n)]
def ref (l c : Nat) (ty : Json) (n : String) (targs : List (String × Json) := []) : Json :=
  node "ref" ty l c [("name", n), ("targs", Json.mkObj targs)]
def arg (v : Json) : Json := Json.mkObj [("value", v)]
def larg (label : String) (v : Json) : Json := Json.mkObj [("label", label), ("value", v)]
def short (label : String) (l c : Nat) : Json := Json.mkObj [("label", label), ("at", pos l c)]
def call (l c : Nat) (ty f : Json) (args : List Json) : Json := node "call" ty l c [("fn", f), ("args", arr args)]
def pipe (l c : Nat) (ty a f : Json) : Json := node "pipe" ty l c [("left", a), ("right", f)]
def bin (l c : Nat) (ty : Json) (op : String) (a b : Json) : Json :=
  node "bin" ty l c [("operator", op), ("left", a), ("right", b)]
def ctor (l c : Nat) (ty : Json) (type variant : String) (args : List Json) : Json :=
  node "ctor" ty l c [("type", type), ("variant", variant), ("args", arr args)]
def update (l c : Nat) (ty : Json) (type variant : String) (record : Json) (fields : List Json) : Json :=
  node "update" ty l c [("type", type), ("variant", variant), ("record", record), ("fields", arr fields)]
def field (l c : Nat) (ty record : Json) (label : String) : Json :=
  node "field" ty l c [("record", record), ("label", label)]
def tuple (l c : Nat) (ty : Json) (items : List Json) : Json := node "tuple" ty l c [("items", arr items)]
def block (l c : Nat) (ty : Json) (stmts : List Json) : Json := node "block" ty l c [("stmts", arr stmts)]
def sLet (l c : Nat) (p v : Json) : Json := Json.mkObj [("stmt", "let"), ("at", pos l c), ("pattern", p), ("value", v)]
def sUse (l c : Nat) (ps : List Json) (f : Json) (annotations : List (Option Json) := []) : Json :=
  let pats := ps.zipIdx.map fun (p, k) =>
    Json.mkObj ([("pattern", p)] ++ ((annotations[k]?.join).map ("annotation", ·)).toList)
  Json.mkObj [("stmt", "use"), ("at", pos l c), ("patterns", arr pats), ("call", f)]
def sExpr (v : Json) : Json := Json.mkObj [("stmt", "expr"), ("value", v)]
def case (l c : Nat) (ty : Json) (subjects clauses : List Json) : Json :=
  node "case" ty l c [("subjects", arr subjects), ("clauses", arr clauses)]
def clause (alts : List (List Json)) (body : Json) (guard : Option Json := none) : Json :=
  Json.mkObj ([("alternatives", arr (alts.map arr)), ("body", body)] ++ (guard.map ("guard", ·)).toList)

def pat (p : String) (ty : Json) (l c : Nat) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("p", Json.str p), ("ty", ty), ("at", pos l c)] ++ fields)
def pVar (l c : Nat) (ty : Json) (n : String) : Json := pat "var" ty l c [("name", n)]
def pDiscard (l c : Nat) (ty : Json) : Json := pat "discard" ty l c [("name", "_")]
def pTuple (l c : Nat) (ty : Json) (items : List Json) : Json := pat "tuple" ty l c [("items", arr items)]
def pCtor (l c : Nat) (ty : Json) (type variant : String) (args : List Json) (spread := false) : Json :=
  pat "ctor" ty l c [("type", type), ("variant", variant), ("args", arr args), ("spread", spread)]
def pArg (p : Json) : Json := Json.mkObj [("pattern", p)]
def pLabel (label : String) (p : Json) : Json := Json.mkObj [("label", label), ("pattern", p)]

def param (label : Option String) (n : String) (ty : Json) : Json :=
  Json.mkObj ((label.map fun l => ("label", Json.str l)).toList ++ [("name", Json.str n), ("ty", ty)])
def function (name : String) (params : List Json) (ret body : Json) (l : Nat := 1) : Json :=
  Json.mkObj [("name", name), ("params", arr params), ("ret", ret), ("body", body), ("at", pos l 1)]
def constant (name : String) (ty value : Json) (l : Nat := 1) : Json :=
  Json.mkObj [("name", name), ("ty", ty), ("value", value), ("at", pos l 1)]
def typeDecl (name : String) (variants : List (String × List (Option String × Json))) (l : Nat := 1) : Json :=
  Json.mkObj [("name", name), ("params", arr []), ("at", pos l 1), ("variants", arr (variants.map fun (v, fs) =>
    Json.mkObj [("name", v), ("fields", arr (fs.map fun (lab, t) =>
      Json.mkObj ((lab.map fun l => ("label", Json.str l)).toList ++ [("ty", t)])))]))]

def alias (name : String) (params : List String) (ty : Json) (l : Nat := 1) : Json :=
  Json.mkObj [("name", name), ("params", arr (params.map Json.str)), ("ty", ty), ("at", pos l 1)]

def program (types functions constants : List Json) (root : String := "m.main") (aliases : List Json := []) : Json :=
  Json.mkObj [("tazuna_ir", 2), ("root", root), ("sources", arr [json% {"module": "m", "path": "src/m.gleam"}]),
    ("types", arr types), ("aliases", arr aliases), ("functions", arr functions), ("constants", arr constants)]

/-- `pub type Box { Box(left: Int, right: String) }` -/
def box : Json := typeDecl "m.Box" [("Box", [(some "left", I), (some "right", S)])]
def boxT : Json := named "m.Box"

/-- `pub type Shape { Circle(r: Int, name: String) Square(r: Int, name: String, side: Int) }` -/
def shape : Json := typeDecl "m.Shape"
  [("Circle", [(some "r", I), (some "name", S)]), ("Square", [(some "r", I), (some "name", S), (some "side", I)])]
def shapeT : Json := named "m.Shape"

/-- `pub fn sub(from a: Int, label b: String) -> Int { a }`: the two parameters have different types, so a call that
places an argument wrongly does not type-check. -/
def sub : Json := function "m.sub" [param "from" "a" I, param "label" "b" S] I (var 1 40 I "a")
def subT : Json := fnT [I, S] I
def subRef (l c : Nat) : Json := ref l c subT "m.sub"

/-- `pub fn twice(f f: fn(Int) -> Int, n n: Int) -> Int { f(f(n)) }` -/
def twice : Json := function "m.twice" [param "f" "f" (fnT [I] I), param "n" "n" I] I
  (call 2 3 I (var 2 3 (fnT [I] I) "f") [arg (call 2 5 I (var 2 5 (fnT [I] I) "f") [arg (var 2 7 I "n")])]) 2

/-- `pub fn id(x: a) -> a { x }` -/
def id : Json := function "m.id" [param none "x" (varT "a")] (varT "a") (var 3 20 (varT "a") "x") 3

def wellTyped : Json := program [box, shape] [sub, twice, id,
  -- `10 |> sub(label: "x")`: the piped value takes the first place no label took, `from`.
  function "m.t1" [] I (pipe 10 3 I (int 10 3 "10") (call 10 9 I (subRef 10 9) [larg "label" (str 10 20 "\"x\"")])) 10,
  -- `"x" |> sub(from: 10)`: here it takes `label`.
  function "m.t2" [] I (pipe 11 3 I (str 11 3 "\"x\"") (call 11 10 I (subRef 11 10) [larg "from" (int 11 20 "10")])) 11,
  -- `sub(label: "x", from: 1)`
  function "m.t3" [] I (call 12 3 I (subRef 12 3) [larg "label" (str 12 15 "\"x\""), larg "from" (int 12 25 "1")]) 12,
  -- `fn t4(label: String) { sub(label:, from: 1) }`
  function "m.t4" [param none "label" S] I (call 13 3 I (subRef 13 3) [short "label" 13 7, larg "from" (int 13 20 "1")]) 13,
  -- `{ use y <- twice(n: 1)  y + 3 }`: the callback takes `f`.
  function "m.t5" [] I (block 14 3 I [
    sUse 14 3 [pVar 14 7 I "y"] (call 14 12 I (ref 14 12 (fnT [fnT [I] I, I] I) "m.twice") [larg "n" (int 14 20 "1")]),
    sExpr (bin 15 3 I "+" (var 15 3 I "y") (int 15 7 "3"))]) 14,
  -- `case s { Circle(name: _, r: x) | Square(r: x, ..) if x > 0 -> x  Circle(r:, ..) -> r  Square(side:, ..) -> side }`
  function "m.t7" [param none "s" shapeT] I (case 16 3 I [var 16 8 shapeT "s"] [
    clause [[pCtor 17 5 shapeT "m.Shape" "Circle" [pLabel "name" (pDiscard 17 18 S), pLabel "r" (pVar 17 24 I "x")]],
            [pCtor 17 30 shapeT "m.Shape" "Square" [pLabel "r" (pVar 17 40 I "x")] true]]
      (var 17 60 I "x") (some (bin 17 50 B ">" (var 17 50 I "x") (int 17 54 "0"))),
    clause [[pCtor 18 5 shapeT "m.Shape" "Circle" [Json.mkObj [("label", "r"), ("at", pos 18 12)]] true]] (var 18 20 I "r"),
    clause [[pCtor 19 5 shapeT "m.Shape" "Square" [Json.mkObj [("label", "side"), ("at", pos 19 12)]] true]]
      (var 19 20 I "side")]) 16,
  -- `fn t8(b: Box) { Box(..b, right: "y") }`
  function "m.t8" [param none "b" boxT] boxT
    (update 20 3 boxT "m.Box" "Box" (var 20 9 boxT "b") [larg "right" (str 20 19 "\"y\"")]) 20,
  -- `fn t9(s: Shape) { let #(a, t) = #(1, "t")  let n = s.r  id(a + n) }`
  function "m.t9" [param none "s" shapeT] I (block 21 3 I [
    sLet 21 3 (pTuple 21 7 (tupT [I, S]) [pVar 21 9 I "a", pVar 21 12 S "t"])
      (tuple 21 17 (tupT [I, S]) [int 21 19 "1", str 21 22 "\"t\""]),
    sLet 22 3 (pVar 22 7 I "n") (field 22 11 I (var 22 11 shapeT "s") "r"),
    sExpr (call 23 3 I (ref 23 3 (fnT [I] I) "m.id" [("a", I)])
      [arg (bin 23 6 I "+" (var 23 6 I "a") (var 23 10 I "n"))])]) 21,
  function "m.big" [] I (int 24 3 "1_000_000_000_000_000_000_000") 24,
  function "m.main" [] S (str 25 3 "\"a\\u{1F600}\\n\\\"\"") 25]
  -- `const table = #(sub, 0)`: a constant holding a function value.
  [constant "m.table" (tupT [subT, I]) (tuple 30 15 (tupT [subT, I]) [subRef 30 17, int 30 22 "0"]) 30]

def loaded (rootTy : Ty) (j : Json) : Except Elab.LoadError (Program rootTy) := Load.load rootTy j

/-- The message of a refused IR with its position, or `accepted`. -/
def verdict (rootTy : Ty) (j : Json) : String :=
  match loaded rootTy j with
  | .ok _ => "accepted"
  | .error e =>
    let place := match e.pos with | some p => s!"{e.file.getD "?"}:{p.line}:{p.col}: " | none => ""
    place ++ e.message

def rootStr : Ty := .fn [] .str

/-- The Int the last definition returns, when it is a function returning a literal. -/
def lastInt {T : List TypeDecl} : {G : List Ty} → Defs T G → Option Int
  | _, .snoc _ _ (.lam (.int n)) => some n
  | _, _ => none

/-- The String the last definition returns, when it is a function returning a literal. -/
def lastStr {T : List TypeDecl} : {G : List Ty} → Defs T G → Option String
  | _, .snoc _ _ (.lam (.str s)) => some s
  | _, _ => none

#guard verdict rootStr wellTyped == "accepted"

/-- A small program around one function `m.main` returning `ret`. -/
def withMain (ret body : Json) (fns : List Json := []) (consts : List Json := []) (aliases : List Json := []) : Json :=
  program [box, shape] ([sub, twice, id] ++ fns ++ [function "m.main" [] ret body 40]) consts (aliases := aliases)

#guard (match loaded rootStr (withMain S (str 40 3 "\"a\\u{1F600}\\n\\\"\"")) with
  | .ok p => lastStr p.defs == some ("a" ++ String.singleton (Char.ofNat 0x1F600) ++ "\n\"")
  | .error _ => false)
#guard (match loaded (.fn [] .int) (withMain I (int 40 3 "1_000_000_000_000_000_000_000")) with
  | .ok p => lastInt p.defs == some 1000000000000000000000
  | .error _ => false)
#guard (match loaded (.fn [] .int) (withMain I (int 40 3 "0x_DEAD_beef")) with
  | .ok p => lastInt p.defs == some 0xDEADBEEF
  | .error _ => false)

-- Swapped labels in a pattern: `Box(right: l, left: r)` with `l: Int`, `r: String` puts each binder on the field of the
-- other type.
#guard verdict (.fn [] .int) (withMain I (case 40 3 I [ctor 40 8 boxT "m.Box" "Box" [arg (int 40 12 "1"), arg (str 40 15 "\"s\"")]]
    [clause [[pCtor 41 5 boxT "m.Box" "Box" [pLabel "right" (pVar 41 16 I "l"), pLabel "left" (pVar 41 25 S "r")]]]
      (var 41 35 I "l")]))
  == "src/m.gleam:41:25: m.main: pattern annotated with a type that is not Int"

-- Swapped labels in a record update: `Box(..b, left: "y")` sets the Int field to a String.
#guard verdict (.fn [] .int) (withMain I (block 40 3 I [
    sLet 40 3 (pVar 40 7 boxT "b") (ctor 40 11 boxT "m.Box" "Box" [arg (int 40 15 "1"), arg (str 40 18 "\"s\"")]),
    sExpr (field 41 3 I (update 41 3 boxT "m.Box" "Box" (var 41 9 boxT "b") [larg "left" (str 41 18 "\"y\"")]) "left")]))
  == "src/m.gleam:41:18: m.main: expected Int, found String"

-- A label the declaration does not have.
#guard verdict (.fn [] .int) (withMain I (field 40 3 I (update 40 3 boxT "m.Box" "Box"
    (ctor 40 9 boxT "m.Box" "Box" [arg (int 40 13 "1"), arg (str 40 16 "\"s\"")]) [larg "middle" (int 40 25 "2")]) "left"))
  == "src/m.gleam:40:3: m.main: Box has no field labelled middle"

-- A pipe placed into the wrong parameter: `10 |> sub(from: 1)` puts 10 into `label: String`.
#guard verdict (.fn [] .int) (withMain I (pipe 40 3 I (int 40 3 "10")
    (call 40 9 I (subRef 40 9) [larg "from" (int 40 20 "1")])))
  == "src/m.gleam:40:3: m.main: expected String, found Int"

-- Positional arguments out of source order: a converter that swapped two arguments.
#guard verdict (.fn [] .int) (withMain I (call 40 3 I (subRef 40 3) [arg (int 40 12 "1"), arg (str 40 7 "\"s\"")]))
  == "src/m.gleam:40:7: m.main: m.sub: positional arguments are out of source order"

-- A wrong type annotation on a node.
#guard verdict (.fn [] .int) (withMain I (bin 40 3 S "+" (int 40 3 "1") (int 40 7 "2")))
  == "src/m.gleam:40:3: m.main: annotated String, computed Int"

-- Recursion through a constant: `const step = #(down, 0)` and `down` reads `step.0`.
#guard verdict (.fn [] .int) (withMain I (int 40 3 "0")
    [function "m.down" [param none "n" I] I (node "index" (fnT [I] I) 50 3
      [("tuple", ref 50 3 (tupT [fnT [I] I, I]) "m.step"), ("index", 0)]) 50]
    [constant "m.step" (tupT [fnT [I] I, I])
      (tuple 51 10 (tupT [fnT [I] I, I]) [ref 51 12 (fnT [I] I) "m.down", int 51 18 "0"]) 51])
  == "src/m.gleam:51:12: m.step: m.down depends on itself: m.down -> m.step -> m.down"

-- Literals Gleam does not accept.
#guard verdict rootStr (withMain S (str 40 3 "\"\\u{D800}\"")) == "src/m.gleam:40:3: m.main: not a Gleam String literal: \"\\u{D800}\""
#guard verdict (.fn [] .int) (withMain I (int 40 3 "1__0")) == "src/m.gleam:40:3: m.main: not a Gleam Int literal: 1__0"

-- A let pattern that can fail.
#guard verdict (.fn [] .int) (withMain I (block 40 3 I [
    sLet 40 3 (pCtor 40 7 shapeT "m.Shape" "Circle" [pArg (pVar 40 14 I "r"), pArg (pDiscard 40 17 S)])
      (ctor 40 22 shapeT "m.Shape" "Circle" [arg (int 40 29 "1"), arg (str 40 32 "\"c\"")]),
    sExpr (var 41 3 I "r")]))
  == "src/m.gleam:40:3: m.main: let pattern can fail to match"

-- Aliases: `type Two(a) = #(a, a)`, `type Count = Int`, `type Counts = Two(Count)`, declared after their use, and
-- `fn pair(n: Count) -> Counts { #(n, n) }`. A function's signature, a field and a node's type may name them.
def aliases : List Json :=
  [alias "m.Counts" [] (json% {"con": "m.Two", "args": [{"con": "m.Count", "args": []}]}) 3,
   alias "m.Two" ["a"] (tupT [varT "a", varT "a"]) 1, alias "m.Count" [] I 2]
#guard verdict (.fn [] .int) (program [typeDecl "m.Tally" [("Tally", [(some "n", named "m.Count")])]]
    [function "m.pair" [param none "n" (named "m.Count")] (named "m.Counts")
      (tuple 5 3 (named "m.Counts") [var 5 5 (named "m.Count") "n", var 5 8 I "n"]) 5,
     function "m.main" [] (named "m.Count")
      (field 6 3 I (ctor 6 3 (named "m.Tally") "m.Tally" "Tally" [larg "n" (int 6 12 "1")]) "n") 6] []
    (aliases := aliases))
  == "accepted"
-- An alias that refers to itself is refused even when nothing uses it.
#guard verdict (.fn [] .int) (withMain I (int 40 3 "1")
    (aliases := [alias "m.Loop" [] (tupT [named "m.Loop", I]) 7]))
  == "src/m.gleam:7:1: m.Loop: type alias m.Loop refers to itself"
#guard verdict (.fn [] .int) (withMain I (int 40 3 "1")
    (aliases := [alias "m.Count" [] (json% {"con": "m.Two", "args": [{"con": "Int", "args": []}, {"con": "Int", "args": []}]}) 2,
      alias "m.Two" ["a"] (tupT [varT "a", varT "a"]) 1]))
  == "src/m.gleam:2:1: m.Count: type alias m.Two takes 1 arguments, given 2"
#guard verdict (.fn [] .int) (withMain I (int 40 3 "1") (aliases := [alias "m.Box" [] I 7]))
  == "type m.Box is declared twice or is built in"

-- A use pattern's annotation: `use y: Int <- twice(n: 1)` holds; `use y: String <- ..` does not.
def useTwice (ann : Json) : Json := block 40 3 I [
  sUse 40 3 [pVar 40 7 I "y"] (call 40 17 I (ref 40 17 (fnT [fnT [I] I, I] I) "m.twice") [larg "n" (int 40 25 "1")])
    [some ann],
  sExpr (var 41 3 I "y")]
#guard verdict (.fn [] .int) (withMain I (useTwice I)) == "accepted"
#guard verdict (.fn [] .int) (withMain I (useTwice S))
  == "src/m.gleam:40:3: m.main: use pattern annotated with a type that is not Int"

-- A block that ends with `let` has the let's value: `{ let #(a, _) = #(7, "s") }` is `#(7, "s")`, and
-- `{ let x = 7 }` is 7.
#guard verdict (.fn [] (.tuple [.int, .str])) (withMain (tupT [I, S]) (block 40 3 (tupT [I, S]) [
    sLet 40 3 (pTuple 40 7 (tupT [I, S]) [pVar 40 9 I "a", pDiscard 40 12 S])
      (tuple 40 17 (tupT [I, S]) [int 40 19 "7", str 40 22 "\"s\""])]))
  == "accepted"
#guard (match loaded (.fn [] .int) (withMain I (block 40 3 I [sLet 40 3 (pVar 40 7 I "x") (int 40 11 "7")])) with
  | .ok p => lastInt p.defs == some 7
  | .error _ => false)
#guard verdict (.fn [] .int) (withMain I (block 40 3 I [
    sLet 40 3 (pCtor 40 7 shapeT "m.Shape" "Circle" [pArg (pVar 40 14 I "r"), pArg (pDiscard 40 17 S)])
      (ctor 40 22 shapeT "m.Shape" "Circle" [arg (int 40 29 "1"), arg (str 40 32 "\"c\"")])]))
  == "src/m.gleam:40:3: m.main: let pattern can fail to match"

-- The root's type.
#guard verdict (Ty.fn [] Ty.spec) (withMain I (int 40 3 "1")) == "src/m.gleam:40:1: root m.main has type fn() -> Int; it must be fn() -> tazuna.Spec"

-- An IR of another version, such as the spike's (which had no `tazuna_ir`).
#guard verdict rootStr (json% {"types": [], "functions": []}) == "missing \"tazuna_ir\" in {\"functions\":[],\"types\":[]}"

end Tazuna.Ir.Examples
