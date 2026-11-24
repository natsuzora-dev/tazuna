import Tazuna.Ir.Elab

/-! Loading a whole IR: the type table, every global's signature, the check that no global depends on itself (through
calls, constants or function values alike), elaboration in dependency order, and the root's type. -/

namespace Tazuna.Ir.Load

open Surface (STy At)
open Elab

/-- The version of the IR's JSON contract this engine reads. -/
def irVersion : Nat := 2

inductive Body where
  | fn (params : List (Option String × String × STy)) (ret : STy) (body : Surface.Expr)
  | const (ty : STy) (value : Surface.Expr)

structure Global where
  name : String
  pos : At
  sig : Sig
  body : Body

def moduleOf (name : String) : String := ".".intercalate (name.splitOn ".").dropLast

/-- Every global reference in an expression, with its position and type arguments. -/
partial def refs : Surface.Expr → List (String × At × List (String × STy))
  | .mk pos _ node =>
    let args (as : List Surface.Arg) := as.flatMap fun | .mk _ _ v => (v.map refs).getD []
    match node with
    | .int _ | .str _ | .var _ => []
    | .ref n targs => [(n, pos, targs)]
    | .ctor _ _ as => args as
    | .field e _ | .index e _ | .un _ e => refs e
    | .update _ _ e fs => refs e ++ args fs
    | .call f as => refs f ++ args as
    | .pipe l r | .bin _ l r => refs l ++ refs r
    | .lam _ _ b => refs b
    | .block stmts => stmts.flatMap fun
      | .let_ _ _ _ v | .expr v => refs v
      | .use _ _ c => refs c
    | .case ss cs => ss.flatMap refs ++ cs.flatMap fun
      | .mk _ g b => (g.map refs).getD [] ++ refs b
    | .list es | .tuple es => es.flatMap refs

def Global.refs (g : Global) : List (String × At × List (String × STy)) :=
  match g.body with
  | .fn _ _ b => Load.refs b
  | .const _ v => Load.refs v

structure St (T : List TypeDecl) where
  G : List Ty
  defs : Defs T G
  /-- Each elaborated instance: global name and type arguments, position from the bottom of `G`, type. -/
  done : List ((String × List Ty) × Nat × Ty)

def St.glob {T : List TypeDecl} (st : St T) (n : String) (args : List Ty) : Option ((t : Ty) × Var st.G t) :=
  match st.done.find? fun ((m, a), _) => m == n && (Ty.sames a args).isSome with
  | some (_, k, t) => (Var.at? st.G (st.G.length - 1 - k) t).map fun v => ⟨t, v⟩
  | none => none

abbrev M (T : List TypeDecl) := StateT (St T) (Except LoadError)

structure Ctx where
  sources : List (String × String)
  globals : List Global

def Ctx.file (c : Ctx) (global : String) : Option String := c.sources.lookup (moduleOf global)

def inGlobal {α T} (c : Ctx) (g : String) (e : E α) : M T α :=
  match e with
  | .ok a => pure a
  | .error (pos, msg) => throw ⟨c.file g, pos, s!"{g}: {msg}"⟩

/-- Elaborates `g` at the type arguments `args`, after every instance its body refers to. Terminates because the
references are acyclic (checked before). -/
partial def demand {T : List TypeDecl} (c : Ctx) (name : String) (args : List Ty) : M T Unit := do
  if ((← get).glob name args).isSome then return
  let some g := c.globals.find? (·.name == name) | throw ⟨none, none, s!"internal: unknown global {name}"⟩
  let σ := g.sig.tvars.zip args
  for (n, pos, targs) in g.refs do
    let some h := c.globals.find? (·.name == n) | throw ⟨c.file g.name, some pos, s!"{g.name}: unknown global {n}"⟩
    let args' ← inGlobal c g.name <| h.sig.tvars.mapM fun v => match targs.lookup v with
      | some t => match toTy T σ t with | .ok t => pure t | .error e => fail pos e
      | none => fail pos s!"{n} needs the type argument {v}"
    demand c n args'
  let st ← get
  let cx : Cx T st.G := { σ, sigs := c.globals.map fun g => (g.name, g.sig), glob := st.glob }
  let ⟨t, body⟩ ← inGlobal c g.name do
    let ty (s : STy) : E Ty := match toTy T σ s with | .ok t => pure t | .error e => fail g.pos e
    match g.body with
    | .fn params ret b =>
      let tys ← params.mapM fun (_, _, s) => ty s
      let rt ← ty ret
      let pl : Scope := (params.map (·.2.1)).zip tys
      let ⟨bt, be⟩ ← elabExpr cx pl b
      let be ← coerce b.pos rt bt be
      let be ← castList (F := fun Γ => Expr T st.G Γ rt) g.pos be (b := tys ++ [])
      pure (⟨.fn tys rt, .lam be⟩ : (t : Ty) × Expr T st.G [] t)
    | .const s v =>
      let want ← ty s
      let ⟨vt, ve⟩ ← elabExpr cx [] v
      pure ⟨want, ← coerce v.pos want vt ve⟩
  set ({ G := t :: st.G, defs := .snoc st.defs t body, done := ((name, args), st.G.length, t) :: st.done } : St T)

/-- Finds a global that depends on itself, reporting the reference that closes the cycle. -/
partial def findCycle (c : Ctx) : Except LoadError Unit := do
  let rec visit (path : List String) (finished : List String) (g : Global) : Except LoadError (List String) := do
    if finished.contains g.name then return finished
    let mut finished := finished
    for (n, pos, _) in g.refs do
      if n == g.name || path.contains n then
        let cycle := (path.reverse.dropWhile (· != n)) ++ [g.name, n]
        throw ⟨c.file g.name, some pos, s!"{g.name}: {n} depends on itself: {" -> ".intercalate cycle}"⟩
      let some h := c.globals.find? (·.name == n) | throw ⟨c.file g.name, some pos, s!"{g.name}: unknown global {n}"⟩
      finished ← visit (g.name :: path) finished h
    return g.name :: finished
  discard <| c.globals.foldlM (fun finished g => visit [] finished g) []

def userTypes (fileOf : String → Option String) (types : List Surface.TypeDef) (aliases : List Surface.AliasDef) :
    Except LoadError (List TypeDecl) := do
  let names := prelude.map (·.name) ++ types.map (·.name) ++ aliases.map (·.name)
  if let some n := nodup names then throw ⟨none, none, s!"type {n} is declared twice or is built in"⟩
  let shells : List TypeDecl := prelude ++ types.map fun t => { name := t.name, params := t.params, variants := [] }
  types.mapM fun t => do
    let err (msg : String) : LoadError := ⟨fileOf t.name, some t.pos, s!"{t.name}: {msg}"⟩
    if builtinName t.name || t.name.startsWith "tazuna." then throw (err "this type belongs to Lean")
    if let some p := nodup t.params then throw (err s!"type parameter {p} is declared twice")
    if let some v := nodup (t.variants.map (·.1)) then throw (err s!"variant {v} is declared twice")
    let σ := t.params.zipIdx.map fun (p, k) => (p, Ty.param k)
    let variants ← t.variants.mapM fun (v, fields) => do
      if let some l := nodup (fields.filterMap (·.1)) then throw (err s!"{v} has the label {l} twice")
      let fields ← fields.mapM fun (l, s) => match toTy shells σ s with
        | .ok ty => pure ({ label := l, ty } : Field)
        | .error e => throw (err e)
      pure ({ name := v, fields } : Variant)
    pure { name := t.name, params := t.params, variants }

/-- Every alias must stand for a type, even one nothing uses: its parameters distinct, its body's type variables among
them, and its expansion free of cycles and well formed. -/
def checkAliases (fileOf : String → Option String) (T : List TypeDecl) (aliases : List Surface.AliasDef) :
    Except LoadError Unit :=
  aliases.forM fun a => do
    let err (msg : String) : LoadError := ⟨fileOf a.name, some a.pos, s!"{a.name}: {msg}"⟩
    if builtinName a.name || a.name.startsWith "tazuna." then throw (err "this type belongs to Lean")
    if let some p := nodup a.params then throw (err s!"type parameter {p} is declared twice")
    if let some v := (tvarsOf [] a.ty).find? (!a.params.contains ·) then throw (err s!"unbound type variable {v}")
    let body ← match Surface.expandAliases aliases [a.name] a.ty with
      | .ok t => pure t
      | .error e => throw (err e)
    match toTy T (a.params.zipIdx.map fun (p, k) => (p, Ty.param k)) body with
    | .ok _ => pure ()
    | .error e => throw (err e)

def globalsOf (fileOf : String → Option String) (p : Surface.Program) : Except LoadError (List Global) := do
  let fns ← p.functions.mapM fun f => do
    let labels := f.params.map (·.1)
    if let some l := nodup (labels.filterMap id) then throw ⟨fileOf f.name, some f.pos, s!"{f.name}: label {l} is declared twice"⟩
    let ty := STy.fn (f.params.map (·.2.2)) f.ret
    pure { name := f.name, pos := f.pos, sig := { tvars := tvarsOf [] ty, labels := some labels, ty },
           body := .fn f.params f.ret f.body : Global }
  let consts ← p.constants.mapM fun c => do
    unless (tvarsOf [] c.ty).isEmpty do throw ⟨fileOf c.name, some c.pos, s!"{c.name}: a constant's type has type variables"⟩
    pure { name := c.name, pos := c.pos, sig := { tvars := [], labels := none, ty := c.ty }, body := .const c.ty c.value }
  let all := fns ++ consts
  if let some n := nodup (all.map (·.name)) then throw ⟨none, none, s!"global {n} is defined twice"⟩
  return all

/-- Loads the IR, requiring the root to be a function of type `rootTy` (the engine asks for `fn() -> tazuna.Spec`). -/
def load (rootTy : Ty) (j : Lean.Json) : Except LoadError (Program rootTy) := do
  let p ← match Surface.readProgram j with
    | .ok p => pure p
    | .error e => throw ⟨none, e.pos, match e.global with | some g => s!"{g}: {e.message}" | none => e.message⟩
  unless p.version == irVersion do
    throw ⟨none, none, s!"IR version {p.version}; this engine reads version {irVersion}"⟩
  let fileOf (g : String) := p.sources.lookup (moduleOf g)
  let user ← userTypes fileOf p.types p.aliases
  let T := prelude ++ user
  checkAliases fileOf T p.aliases
  let globals ← globalsOf fileOf p
  let c : Ctx := { sources := p.sources, globals }
  findCycle c
  let some root := globals.find? (·.name == p.root) | throw ⟨none, none, s!"root {p.root} is not defined"⟩
  let run : M T Unit := do
    for g in globals do
      demand c g.name (g.sig.tvars.zipIdx.map fun (_, k) => Ty.param k)
  let ((), st) ← run.run { G := [], defs := .nil, done := [] }
  unless root.sig.tvars.isEmpty && root.sig.labels.isSome do
    throw ⟨c.file root.name, some root.pos, s!"root {root.name} must be a function without type variables"⟩
  let some ⟨t, v⟩ := st.glob root.name [] | throw ⟨none, none, "internal: root not elaborated"⟩
  match Ty.same t rootTy with
  | some ⟨h⟩ => pure { types := T, globals := st.G, defs := st.defs, root := h ▸ v }
  | none => throw ⟨c.file root.name, some root.pos,
      s!"root {root.name} has type {showTy T t}; it must be {showTy T rootTy}"⟩

end Tazuna.Ir.Load
