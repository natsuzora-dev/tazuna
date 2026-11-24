import Tazuna.Ir.Core
import Tazuna.Ir.Literal
import Tazuna.Ir.Surface

/-! Elaboration of the converter's IR into typed terms. This is where Gleam's surface syntax gets its meaning:

- Arguments: labelled arguments go to the parameter or field with that label; unlabelled ones fill the remaining
  places in order. Positional arguments must appear in source order.
- `a |> f(b)` is `f(a, b)` when `f` takes one more argument than given, and `f(b)(a)` otherwise; `a |> f` is `f(a)`.
- `use p <- f(a)` followed by the rest of the block is `f(a, fn(p) { rest })`, the callback filling a place like an
  unlabelled argument written last. A `use` call node's type is the type of that whole call; so is the type of a call
  node a pipe inserts into.
- `let p = e` followed by the rest of the block matches `e` against `p`, which must be irrefutable. A block that ends
  with `let p = e` has the value of `e`.
- Type aliases are expanded when the IR is read (`Tazuna.Ir.Surface.readTy`), so elaboration never sees one.
- `case a, b { p, q | r, s -> .. }` matches the tuple `#(a, b)`; each alternative is its own clause.
- A labelled argument or pattern without a value is the variable named by the label.

Every global is elaborated once for each instantiation it is used at (and once with its type variables kept rigid), in
dependency order, so the program has no cycles by construction. -/

namespace Tazuna.Ir.Elab

open Surface (STy At)

/-- An error inside one global, at a position when one is known. -/
abbrev E := Except (Option At × String)

def fail {α} (pos : At) (msg : String) : E α := throw (some pos, msg)

/-- A failure to load an IR. It is always a converter bug, so the engine reports it as an internal error. -/
structure LoadError where
  file : Option String
  pos : Option At
  message : String

def nodup (xs : List String) : Option String :=
  match xs with
  | [] => none
  | x :: rest => if rest.contains x then some x else nodup rest

/-- What the elaborator knows about a global before elaborating its body. -/
structure Sig where
  tvars : List String
  /-- The parameters' labels for a function called by name; `none` for a constant. -/
  labels : Option (List (Option String))
  ty : STy

/-- The type variables of a signature, in order of first appearance. -/
partial def tvarsOf (acc : List String) : STy → List String
  | .var n => if acc.contains n then acc else acc ++ [n]
  | .con _ args | .tuple args => args.foldl tvarsOf acc
  | .fn ps r => tvarsOf (ps.foldl tvarsOf acc) r
  | .hole _ => acc

def builtinName (n : String) : Bool := n == "Int" || n == "String" || n == "List"

section
variable (T : List TypeDecl)

def typeIndex (name : String) : Option Nat := T.findIdx? (·.name == name)

partial def showTy : Ty → String
  | .int => "Int"
  | .str => "String"
  | .list t => s!"List({showTy t})"
  | .tuple ts => "#(" ++ ", ".intercalate (ts.map showTy) ++ ")"
  | .fn ps r => "fn(" ++ ", ".intercalate (ps.map showTy) ++ ") -> " ++ showTy r
  | .adt i args _ =>
    let n := (T[i]?.map (·.name)).getD s!"type{i}"
    if args.isEmpty then n else n ++ "(" ++ ", ".intercalate (args.map showTy) ++ ")"
  | .param k => s!"param{k}"

/-- Converts a type written in the IR, with `σ` giving the type variables in scope. -/
partial def toTy (σ : List (String × Ty)) : STy → Except String Ty
  | .con "Int" [] => pure .int
  | .con "String" [] => pure .str
  | .con "List" [t] => return .list (← toTy σ t)
  | .con n args => do
    let some i := typeIndex T n | throw s!"unknown type {n}"
    let some d := T[i]? | throw s!"unknown type {n}"
    if builtinName n || d.params.length != args.length then
      throw s!"type {n} takes {d.params.length} arguments, given {args.length}"
    let args ← args.mapM (toTy σ)
    return .adt i args (d.variantTys args)
  | .fn ps r => return .fn (← ps.mapM (toTy σ)) (← toTy σ r)
  | .tuple ts => return .tuple (← ts.mapM (toTy σ))
  | .var n => match σ.lookup n with
    | some t => pure t
    | none => throw s!"unbound type variable {n}"
  | .hole h => throw s!"a node's type has a hole {h}"

/-- Whether a source annotation fits a type: holes and type variables the annotation introduces fit anything. -/
partial def annotationFits (σ : List (String × Ty)) : STy → Ty → Bool
  | .hole _, _ => true
  | .var n, t => match σ.lookup n with
    | some u => (Ty.same u t).isSome
    | none => true
  | .con "Int" [], .int | .con "String" [], .str => true
  | .con "List" [a], .list t => annotationFits σ a t
  | .con n args, .adt i ts _ =>
    typeIndex T n == some i && args.length == ts.length && (args.zip ts).all fun (a, t) => annotationFits σ a t
  | .fn ps r, .fn qs u =>
    ps.length == qs.length && (ps.zip qs).all (fun (a, t) => annotationFits σ a t) && annotationFits σ r u
  | .tuple as, .tuple ts => as.length == ts.length && (as.zip ts).all fun (a, t) => annotationFits σ a t
  | _, _ => false

end

/-- Local variables, the innermost first; the empty name binds a value nothing can refer to. -/
abbrev Scope := List (String × Ty)

def ctx (sc : Scope) : List Ty := sc.map Prod.snd

def lookupVar : (sc : Scope) → String → Option ((t : Ty) × Var (ctx sc) t)
  | [], _ => none
  | (n, t) :: sc, x =>
    if n == x then some ⟨t, .here⟩ else (lookupVar sc x).map fun ⟨u, v⟩ => ⟨u, .there v⟩

def castList {F : List Ty → Type} {a b : List Ty} (pos : At) (x : F a) : E (F b) :=
  match Ty.sames a b with
  | some ⟨h⟩ => pure (h ▸ x)
  | none => fail pos "internal: context mismatch"

section Patterns
variable (T : List TypeDecl) (σ : List (String × Ty))

/-- An argument of a call, constructor or constructor pattern, placed by label or by position. -/
structure Placed (α : Type) where
  pos : At
  label : Option String
  value : α

/-- Gleam's argument placement. `labels` are the parameters' labels; positional arguments come before labelled ones
in the source, in source order, and fill the places no label took. `spread` fills the places left over with `none`. -/
def place {α} (pos : At) (what : String) (labels : List (Option String)) (first : List α) (args : List (Placed α))
    (last : List α) (spread : Bool) : E (List (Option α)) := do
  let positional := args.filter (·.label.isNone)
  let labelled := args.filterMap fun a => a.label.map fun l => (l, a)
  if let some a := (args.dropWhile (·.label.isNone)).find? (·.label.isNone) then
    fail a.pos s!"{what}: an unlabelled argument follows a labelled one"
  for (a, b) in positional.zip positional.tail do
    unless a.pos.lt b.pos do fail b.pos s!"{what}: positional arguments are out of source order"
  if let some l := nodup (labelled.map (·.1)) then fail pos s!"{what}: label {l} is given twice"
  for (l, a) in labelled do
    unless labels.contains (some l) do fail a.pos s!"{what} has no label {l}"
  let free := labels.filter fun l => match l with
    | some l => !(labelled.any (·.1 == l))
    | none => true
  let rest := first ++ positional.map (·.value) ++ last
  if rest.length > free.length || (rest.length < free.length && !spread) then
    fail pos s!"{what} takes {labels.length} arguments, given {rest.length + labelled.length}"
  let (out, _) := labels.foldl (init := ([], rest)) fun (out, rest) l =>
    match l.bind fun l => labelled.lookup l with
    | some a => (out ++ [some a.value], rest)
    | none => match rest with
      | x :: xs => (out ++ [some x], xs)
      | [] => (out ++ [none], [])
  return out

def castPat {Δ : List Ty} (pos : At) (u t : Ty) (p : Pat u Δ) : E (Pat t Δ) :=
  match Ty.same u t with
  | some ⟨h⟩ => pure (h ▸ p)
  | none => fail pos s!"pattern for {showTy T u} on {showTy T t}"

def checkPatTy (pos : At) (ann : STy) (t : Ty) : E Unit :=
  if annotationFits T σ ann t then pure () else fail pos s!"pattern annotated with a type that is not {showTy T t}"

def lookupDecl (pos : At) (name : String) : E ((i : Nat) × (d : TypeDecl) × PLift (T[i]? = some d)) := do
  let some i := typeIndex T name | fail pos s!"unknown type {name}"
  match h : T[i]? with
  | some d => pure ⟨i, d, ⟨h⟩⟩
  | none => fail pos s!"unknown type {name}"

/-- The variant's index into a type's variants `vs`, and its fields' labels. -/
def variantIndex (pos : At) (d : TypeDecl) (vs : List (List Ty)) (name : String) :
    E (Fin vs.length × List (Option String)) :=
  match d.variants.findIdx? (·.name == name) with
  | some k => match d.variants[k]? with
    | some v => if hk : k < vs.length then pure (⟨k, hk⟩, v.fields.map (·.label)) else fail pos "internal: variant index"
    | none => fail pos "internal: variant index"
  | none => fail pos s!"{d.name} has no variant {name}"

mutual
partial def elabPat (t : Ty) : Surface.Pat → E ((Δ : Scope) × Pat t (ctx Δ))
  | .mk pos ann node => do
    checkPatTy T σ pos ann t
    match node with
    | .discard _ => pure ⟨[], .wild⟩
    | .var n => pure ⟨[(n, t)], .bind⟩
    | .int text =>
      let some n := Literal.parseInt text | fail pos s!"not a Gleam Int literal: {text}"
      match Ty.same .int t with
      | some ⟨h⟩ => pure ⟨[], h ▸ .int n⟩
      | none => fail pos s!"Int pattern on {showTy T t}"
    | .str text =>
      let some s := Literal.parseStr text | fail pos s!"not a Gleam String literal: {text}"
      match Ty.same .str t with
      | some ⟨h⟩ => pure ⟨[], h ▸ .str s⟩
      | none => fail pos s!"String pattern on {showTy T t}"
    | .tuple items =>
      match t with
      | .tuple ts =>
        unless ts.length == items.length do fail pos s!"tuple pattern of {items.length} on {showTy T (.tuple ts)}"
        let ⟨Δ, ps⟩ ← elabPats ts items
        pure ⟨Δ, ← castPat T pos (.tuple ts) t (.tuple ps)⟩
      | t => fail pos s!"tuple pattern on {showTy T t}"
    | .ctor type variant args spread =>
      let ⟨i, d, _⟩ ← lookupDecl T pos type
      match t with
      | .adt j targs vs =>
      unless i == j do fail pos s!"{type}.{variant} pattern on {showTy T t}"
      let (v, labels) ← variantIndex pos d vs variant
      let placed := args.map fun | .mk p l pat => ({ pos := p, label := l, value := pat } : Placed _)
      let slots ← place pos s!"pattern {variant}" labels [] placed [] spread
      let pats := (slots.zip labels).map fun
        | (some (some p), _) => p
        | (some none, some l) => .mk pos (.hole "_") (.var l)
        | _ => .mk pos (.hole "_") (.discard "_")
      let ⟨Δ, ps⟩ ← elabPats (vs.get v) pats
      pure ⟨Δ, ← castPat T pos (.adt j targs vs) t (.ctor v ps)⟩
      | t => fail pos s!"{type}.{variant} pattern on {showTy T t}"
    | .as p n =>
      let ⟨Δ, p'⟩ ← elabPat t p
      let p'' ← castList (F := Pat t) pos (Pat.as p')
      pure ⟨Δ ++ [(n, t)], p''⟩

partial def elabPats : (ts : List Ty) → List Surface.Pat → E ((Δ : Scope) × Pats ts (ctx Δ))
  | [], [] => pure ⟨[], .nil⟩
  | t :: ts, p :: ps => do
    let ⟨Δ, p'⟩ ← elabPat t p
    let ⟨Δ', ps'⟩ ← elabPats ts ps
    let r ← castList (F := Pats (t :: ts)) (match p with | .mk pos .. => pos) (Pats.cons p' ps')
    pure ⟨Δ ++ Δ', r⟩
  | _, _ => throw (none, "internal: pattern count")
end

/-- The pattern's variables, checked to be distinct. -/
def elabPatTop (pos : At) (t : Ty) (p : Surface.Pat) : E ((Δ : Scope) × Pat t (ctx Δ)) := do
  let r ← elabPat T σ t p
  if let some n := nodup (r.1.map (·.1) |>.filter (· != "")) then fail pos s!"pattern binds {n} twice"
  return r

end Patterns

mutual
partial def Pat.irrefutable {t : Ty} {Δ : List Ty} : Pat t Δ → Bool
  | .wild | .bind => true
  | .int _ | .str _ => false
  | .tuple ps => Pats.irrefutable ps
  | @Pat.ctor _ _ vs _ _ ps => vs.length == 1 && Pats.irrefutable ps
  | .as p => Pat.irrefutable p
partial def Pats.irrefutable {ts : List Ty} {Δ : List Ty} : Pats ts Δ → Bool
  | .nil => true
  | .cons p ps => Pat.irrefutable p && Pats.irrefutable ps
end

/-- What elaborating one body needs: the type table, the type variables in scope, every global's signature, and the
instances already elaborated (all a body refers to). -/
structure Cx (T : List TypeDecl) (G : List Ty) where
  σ : List (String × Ty)
  sigs : List (String × Sig)
  glob : String → List Ty → Option ((t : Ty) × Var G t)

/-- What fills a parameter or field: an expression from the source, a piped value already elaborated, or a `use`
callback with its patterns and the rest of the block. -/
inductive Slot (T : List TypeDecl) (G : List Ty) (Γ : List Ty) where
  | expr (e : Surface.Expr)
  | typed (pos : At) (t : Ty) (e : Expr G Γ t)
  | callback (pos : At) (patterns : List (Surface.Pat × Option STy)) (rest : List Surface.Stmt)

section Exprs
variable {T : List TypeDecl} {G : List Ty} (cx : Cx T G)

def toTyAt (pos : At) (t : STy) : E Ty :=
  match toTy T cx.σ t with
  | .ok t => pure t
  | .error e => fail pos e

def coerce {Γ : List Ty} (pos : At) (want got : Ty) (e : Expr G Γ got) : E (Expr G Γ want) :=
  let _ := cx
  match Ty.same got want with
  | some ⟨h⟩ => pure (h ▸ e)
  | none => fail pos s!"expected {showTy T want}, found {showTy T got}"

/-- Checks a node's type annotation against the type computed from its children. -/
def annotated {Γ : List Ty} (pos : At) (ann : STy) (r : (t : Ty) × Expr G Γ t) : E ((t : Ty) × Expr G Γ t) := do
  if let .hole _ := ann then return r
  let want ← toTyAt cx pos ann
  match Ty.same r.1 want with
  | some _ => pure r
  | none => fail pos s!"annotated {showTy T want}, computed {showTy T r.1}"

def elabBin {Γ : List Ty} (pos : At) (op : String) (a : Ty) (l : Expr G Γ a) (b : Ty) (r : Expr G Γ b) :
    E ((c : Ty) × Expr G Γ c) := do
  let ints (o : BinOp .int .int .int) : E ((c : Ty) × Expr G Γ c) := do
    return ⟨.int, Expr.bin o (← coerce cx pos .int a l) (← coerce cx pos .int b r)⟩
  let cmp (o : BinOp .int .int .bool) : E ((c : Ty) × Expr G Γ c) := do
    return ⟨.bool, Expr.bin o (← coerce cx pos .int a l) (← coerce cx pos .int b r)⟩
  let logic (o : BinOp .bool .bool .bool) : E ((c : Ty) × Expr G Γ c) := do
    return ⟨.bool, Expr.bin o (← coerce cx pos .bool a l) (← coerce cx pos .bool b r)⟩
  match op with
  | "+" => ints .add | "-" => ints .sub | "*" => ints .mul | "/" => ints .div | "%" => ints .mod
  | "<" => cmp .lt | "<=" => cmp .le | ">" => cmp .gt | ">=" => cmp .ge
  | "&&" => logic .and | "||" => logic .or
  | "<>" => return ⟨.str, Expr.bin .concat (← coerce cx pos .str a l) (← coerce cx pos .str b r)⟩
  | "==" | "!=" =>
    if h : a.comparable = true then
      let r ← coerce cx pos a b r
      return ⟨.bool, Expr.bin (if op == "==" then .eq h else .ne h) l r⟩
    else fail pos s!"{op} on {showTy T a}, whose values include functions"
  | _ => fail pos s!"unknown operator {op}"

def shorthand (pos : At) (label : String) : Surface.Expr := .mk pos (.hole "_") (.var label)

def placedArgs {Γ : List Ty} (args : List Surface.Arg) : List (Placed (Slot T G Γ)) :=
  args.map fun
    | .mk pos label (some v) => { pos, label, value := .expr v }
    | .mk pos label none => { pos, label, value := .expr (shorthand pos (label.getD "")) }

mutual
partial def elabExpr (sc : Scope) : Surface.Expr → E ((t : Ty) × Expr G (ctx sc) t)
  | .mk pos ann node => do
    let r : (t : Ty) × Expr G (ctx sc) t ← match node with
    | .int text =>
      let some n := Literal.parseInt text | fail pos s!"not a Gleam Int literal: {text}"
      pure ⟨.int, .int n⟩
    | .str text =>
      let some s := Literal.parseStr text | fail pos s!"not a Gleam String literal: {text}"
      pure ⟨.str, .str s⟩
    | .var n =>
      let some ⟨t, v⟩ := lookupVar sc n | fail pos s!"unbound variable {n}"
      pure ⟨t, .var v⟩
    | .ref n targs =>
      let some sig := cx.sigs.lookup n | fail pos s!"unknown global {n}"
      let keys := targs.map (·.1)
      unless keys.length == sig.tvars.length && sig.tvars.all keys.contains && (nodup keys).isNone do
        fail pos s!"{n} takes type arguments for [{", ".intercalate sig.tvars}], given [{", ".intercalate keys}]"
      let args ← sig.tvars.mapM fun v => match targs.lookup v with
        | some t => toTyAt cx pos t
        | none => fail pos s!"missing type argument {v}"
      let some ⟨t, v⟩ := cx.glob n args | fail pos s!"internal: {n} is not elaborated"
      pure ⟨t, .global v⟩
    | .ctor type variant args =>
      let ⟨i, d, _⟩ ← lookupDecl T pos type
      let want ← toTyAt cx pos ann
      let .adt j targs vs := want | fail pos s!"{type}.{variant} annotated {showTy T want}"
      unless i == j do fail pos s!"{type}.{variant} annotated {showTy T want}"
      let (v, labels) ← variantIndex pos d vs variant
      if args.isEmpty && !labels.isEmpty then
        fail pos s!"{variant} used as a function value"
      let slots ← place pos s!"constructor {variant}" labels [] (placedArgs args) [] false
      let es ← elabSlots sc pos (vs.get v) slots
      pure ⟨.adt i targs vs, .ctor v es⟩
    | .field record label =>
      let ⟨rt, re⟩ ← elabExpr sc record
      let .adt i targs vs := rt | fail pos s!"field {label} of {showTy T rt}"
      let re ← coerce cx pos (.adt i targs vs) rt re
      let some d := T[i]? | fail pos "internal: type index"
      let some (k, ft) := d.accessor label
        | fail pos s!"{d.name} has no field labelled {label} shared by every variant"
      let ft := ft.inst targs
      let some ⟨hk⟩ := Ty.fieldAt k ft vs | fail pos s!"internal: field {label} of {showTy T rt}"
      pure ⟨ft, .field label k hk re⟩
    | .index tuple k =>
      let ⟨tt, te⟩ ← elabExpr sc tuple
      let .tuple ts := tt | fail pos s!"index {k} of {showTy T tt}"
      let te ← coerce cx pos (.tuple ts) tt te
      if hk : k < ts.length then pure ⟨ts.get ⟨k, hk⟩, .index te ⟨k, hk⟩⟩
      else fail pos s!"index {k} of a tuple of {ts.length}"
    | .update type variant record fields =>
      let ⟨i, d, _⟩ ← lookupDecl T pos type
      let ⟨rt, re⟩ ← elabExpr sc record
      let .adt j targs vs := rt | fail pos s!"record update of {showTy T rt}"
      unless i == j do fail pos s!"{variant} update of {showTy T rt}"
      let (_, labels) ← variantIndex pos d vs variant
      let [fs] := vs | fail pos s!"record update on {type}, which has several variants"
      let given ← fields.mapM fun
        | .mk _ (some l) (some e) => pure (l, Slot.expr (G := G) (Γ := ctx sc) e)
        | .mk p (some l) none => pure (l, Slot.expr (shorthand p l))
        | .mk p none _ => fail p "a record update field needs a label"
      if let some l := nodup (given.map (·.1)) then fail pos s!"record update sets {l} twice"
      for (l, _) in given do
        unless labels.contains (some l) do fail pos s!"{variant} has no field labelled {l}"
      let re ← coerce cx pos (.adt i targs [fs]) rt re
      let p ← elabPatch sc pos labels fs given
      pure ⟨.adt i targs [fs], .update re p⟩
    | .call f args => elabCall sc pos f args [] []
    | .pipe left right =>
      let ⟨lt, le⟩ ← elabExpr sc left
      let piped := Slot.typed left.pos lt le
      match right with
      | .mk rpos rann (.call f args) =>
        let ⟨ft, _⟩ ← elabExpr sc f
        match ft with
        | .fn ps _ =>
          if ps.length == args.length + 1 then
            annotated cx rpos rann (← elabCall sc rpos f args [piped] [])
          else applyTo sc pos right piped
        | _ => applyTo sc pos right piped
      | _ => applyTo sc pos right piped
    | .lam params ret body =>
      let tys ← params.mapM fun | .mk _ t _ => toTyAt cx pos t
      for (p, t) in params.zip tys do
        let .mk n _ a := p
        if let some a := a then
          unless annotationFits T cx.σ a t do fail pos s!"parameter {n} annotated with a type that is not {showTy T t}"
      let pl : Scope := (params.map fun | .mk n _ _ => n).zip tys
      let ⟨bt, be⟩ ← elabExpr (pl ++ sc) body
      if let some a := ret then
        unless annotationFits T cx.σ a bt do fail pos s!"return annotated with a type that is not {showTy T bt}"
      let be ← castList (F := fun Γ => Expr G Γ bt) pos be (b := tys ++ ctx sc)
      pure ⟨.fn tys bt, .lam be⟩
    | .block stmts => elabBlock sc pos stmts
    | .case subjects clauses =>
      let want ← toTyAt cx pos ann
      match subjects with
      | [s] =>
        let ⟨st, se⟩ ← elabExpr sc s
        let cs ← elabClauses sc pos st want (fun alt => match alt with
          | [p] => elabPatTop T cx.σ pos st p
          | _ => fail pos "a clause alternative has a pattern per subject") clauses
        pure ⟨want, .case se cs⟩
      | _ =>
        let ⟨sts, ses⟩ ← elabExprs sc subjects
        let cs ← elabClauses sc pos (.tuple sts) want (fun alt => do
          unless alt.length == sts.length do fail pos "a clause alternative has a pattern per subject"
          let ⟨Δ, ps⟩ ← elabPats T cx.σ sts alt
          if let some n := nodup (Δ.map (·.1) |>.filter (· != "")) then fail pos s!"pattern binds {n} twice"
          pure ⟨Δ, .tuple ps⟩) clauses
        pure ⟨want, .case (.tuple ses) cs⟩
    | .list items =>
      let want ← toTyAt cx pos ann
      let .list t := want | fail pos s!"list annotated {showTy T want}"
      pure ⟨.list t, .list (← elabItems sc t items)⟩
    | .tuple items =>
      let ⟨ts, es⟩ ← elabExprs sc items
      pure ⟨.tuple ts, .tuple es⟩
    | .bin op l r =>
      let ⟨lt, le⟩ ← elabExpr sc l
      let ⟨rt, re⟩ ← elabExpr sc r
      elabBin cx pos op lt le rt re
    | .un op e =>
      let ⟨t, e⟩ ← elabExpr sc e
      match op with
      | "!" => pure ⟨.bool, .not (← coerce cx pos .bool t e)⟩
      | "-" => pure ⟨.int, .neg (← coerce cx pos .int t e)⟩
      | _ => fail pos s!"unknown operator {op}"
    annotated cx pos ann r

/-- `f(args)` with extra unlabelled arguments before (a pipe) or after (a `use` callback) the written ones. -/
partial def elabCall (sc : Scope) (pos : At) (f : Surface.Expr) (args : List Surface.Arg)
    (first last : List (Slot T G (ctx sc))) : E ((t : Ty) × Expr G (ctx sc) t) := do
  let ⟨ft, fe⟩ ← elabExpr sc f
  let .fn ps r := ft | fail pos s!"call of {showTy T ft}"
  let fe ← coerce cx pos (.fn ps r) ft fe
  let labels := match f with
    | .mk _ _ (.ref n _) => ((cx.sigs.lookup n).bind (·.labels)).getD (ps.map fun _ => none)
    | _ => ps.map fun _ => none
  let what := match f with | .mk _ _ (.ref n _) => n | _ => "the function"
  let slots ← place pos what labels first (placedArgs args) last false
  pure ⟨r, .call fe (← elabSlots sc pos ps slots)⟩

partial def applyTo (sc : Scope) (pos : At) (f : Surface.Expr) (arg : Slot T G (ctx sc)) :
    E ((t : Ty) × Expr G (ctx sc) t) := do
  let ⟨ft, fe⟩ ← elabExpr sc f
  let .fn [p] r := ft | fail pos s!"pipe into {showTy T ft}, which does not take one argument"
  let fe ← coerce cx pos (.fn [p] r) ft fe
  pure ⟨r, .call fe (.cons (← elabSlot sc p arg) .nil)⟩

partial def elabSlot (sc : Scope) (t : Ty) : Slot T G (ctx sc) → E (Expr G (ctx sc) t)
  | .expr e => do
    let ⟨u, x⟩ ← elabExpr sc e
    coerce cx e.pos t u x
  | .typed pos u x => coerce cx pos t u x
  | .callback pos pats rest => do
    let .fn ps r := t | fail pos s!"use callback where {showTy T t} is expected"
    unless ps.length == pats.length do fail pos s!"use binds {pats.length} values; the callback takes {ps.length}"
    for ((_, ann), t) in pats.zip ps do
      if let some a := ann then
        unless annotationFits T cx.σ a t do fail pos s!"use pattern annotated with a type that is not {showTy T t}"
    let named := pats.mapIdx fun k (p, _) => match p with
      | .mk _ _ (.var n) => (n, none)
      | .mk _ _ (.discard _) => ("", none)
      | p => (s!"use pattern {k}", some p)
    let lets := named.filterMap fun (n, p) => p.map fun p => Surface.Stmt.let_ pos p none (.mk pos (.hole "_") (.var n))
    let pl : Scope := (named.map (·.1)).zip ps
    let ⟨bt, be⟩ ← elabBlock (pl ++ sc) pos (lets ++ rest)
    let be ← coerce cx pos r bt be
    let be ← castList (F := fun Γ => Expr G Γ r) pos be (b := ps ++ ctx sc)
    coerce cx pos t (.fn ps r) (.lam be)

partial def elabSlots (sc : Scope) (pos : At) :
    (ts : List Ty) → List (Option (Slot T G (ctx sc))) → E (Exprs G (ctx sc) ts)
  | [], [] => pure .nil
  | t :: ts, some s :: ss => do pure (.cons (← elabSlot sc t s) (← elabSlots sc pos ts ss))
  | _ :: _, none :: _ => fail pos "an argument is missing"
  | _, _ => fail pos "internal: argument count"

partial def elabPatch (sc : Scope) (pos : At) :
    List (Option String) → (ts : List Ty) → List (String × Slot T G (ctx sc)) → E (Patch G (ctx sc) ts)
  | l :: ls, t :: ts, given => do
    let rest ← elabPatch sc pos ls ts given
    match l.bind fun l => given.lookup l with
    | some s => pure (.set (← elabSlot sc t s) rest)
    | none => pure (.keep rest)
  | [], [], _ => pure .nil
  | _, _, _ => fail pos "internal: field count"

partial def elabExprs (sc : Scope) : List Surface.Expr → E ((ts : List Ty) × Exprs G (ctx sc) ts)
  | [] => pure ⟨[], .nil⟩
  | e :: es => do
    let ⟨t, x⟩ ← elabExpr sc e
    let ⟨ts, xs⟩ ← elabExprs sc es
    pure ⟨t :: ts, .cons x xs⟩

partial def elabItems (sc : Scope) (t : Ty) : List Surface.Expr → E (Items G (ctx sc) t)
  | [] => pure .nil
  | e :: es => do
    let ⟨u, x⟩ ← elabExpr sc e
    pure (.cons (← coerce cx e.pos t u x) (← elabItems sc t es))

partial def elabBlock (sc : Scope) (pos : At) : List Surface.Stmt → E ((t : Ty) × Expr G (ctx sc) t)
  | [] => fail pos "empty block"
  | [.expr e] => elabExpr sc e
  | [.let_ p pat ann value] => do
    let ⟨t, x⟩ ← elabExpr sc value
    if let some a := ann then
      unless annotationFits T cx.σ a t do fail p s!"let annotated with a type that is not {showTy T t}"
    let ⟨_, pat'⟩ ← elabPatTop T cx.σ p t pat
    unless Pat.irrefutable pat' do fail p "let pattern can fail to match"
    pure ⟨t, x⟩
  | [.use p ..] => fail p "a block ends with use"
  | .expr e :: rest => do
    let ⟨t, x⟩ ← elabExpr sc e
    let ⟨r, body⟩ ← elabBlock (("", t) :: sc) pos rest
    pure ⟨r, .let_ x body⟩
  | .let_ p pat ann value :: rest => do
    let ⟨t, x⟩ ← elabExpr sc value
    if let some a := ann then
      unless annotationFits T cx.σ a t do fail p s!"let annotated with a type that is not {showTy T t}"
    match pat with
    | .mk ppos pann (.var n) =>
      checkPatTy T cx.σ ppos pann t
      let ⟨r, body⟩ ← elabBlock ((n, t) :: sc) pos rest
      pure ⟨r, .let_ x body⟩
    | _ =>
      let ⟨Δ, pat'⟩ ← elabPatTop T cx.σ p t pat
      unless Pat.irrefutable pat' do fail p "let pattern can fail to match"
      let ⟨r, body⟩ ← elabBlock (Δ ++ sc) pos rest
      let body ← castList (F := fun Γ => Expr G Γ r) p body (b := ctx Δ ++ ctx sc)
      pure ⟨r, .case x (.cons pat' body .nil)⟩
  | .use p pats call :: rest => do
    let cb := Slot.callback p pats rest
    match call with
    | .mk cpos cann (.call f args) => annotated cx cpos cann (← elabCall sc cpos f args [] [cb])
    | f => elabCall sc p f [] [] [cb]

partial def elabClauses (sc : Scope) (pos : At) (st r : Ty)
    (pat : List Surface.Pat → E ((Δ : Scope) × Pat st (ctx Δ))) :
    List Surface.Clause → E (Clauses G (ctx sc) st r)
  | [] => pure .nil
  | .mk alts guard body :: rest => do
    let rest ← elabClauses sc pos st r pat rest
    let elabAlt (alt : List Surface.Pat) (rest : Clauses G (ctx sc) st r) : E (Clauses G (ctx sc) st r) := do
      let ⟨Δ, p⟩ ← pat alt
      let ⟨bt, be⟩ ← elabExpr (Δ ++ sc) body
      let be ← coerce cx body.pos r bt be
      let be ← castList (F := fun Γ => Expr G Γ r) pos be (b := ctx Δ ++ ctx sc)
      match guard with
      | none => pure (.cons p be rest)
      | some g =>
        let ⟨gt, ge⟩ ← elabExpr (Δ ++ sc) g
        let ge ← coerce cx g.pos .bool gt ge
        let ge ← castList (F := fun Γ => Expr G Γ .bool) pos ge (b := ctx Δ ++ ctx sc)
        pure (.guarded p ge be rest)
    let bound ← alts.mapM fun alt => do
      let ⟨Δ, _⟩ ← pat alt
      pure (((Δ.filter (·.1 != "")).map fun (n, t) => (n, showTy T t)).mergeSort fun a b => a.1 ≤ b.1)
    if let b :: bs := bound then
      unless bs.all (· == b) do fail pos "alternatives bind different variables"
    else fail pos "a clause has no pattern"
    alts.foldrM elabAlt rest
end

end Exprs

end Tazuna.Ir.Elab
