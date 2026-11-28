import Tazuna.Ir.Elab
import Tazuna.Semantics.Sites

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

-- An argument or clause without an expression references nothing.
set_option linter.tazuna.silentDefault false in
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
    | .capture _ f bs as => refs f ++ args bs ++ args as
    | .pipe l r | .bin _ l r => refs l ++ refs r
    | .lam _ _ b => refs b
    | .block stmts => stmts.flatMap fun
      | .let_ _ _ _ v | .expr v => refs v
      | .use _ _ c => refs c
    | .case ss cs => ss.flatMap refs ++ cs.flatMap fun
      | .mk _ g b => (g.map refs).getD [] ++ refs b
    | .list es | .tuple es => es.flatMap refs

/-- The references to other globals; built-ins are not globals. -/
def Global.refs (g : Global) : List (String × At × List (String × STy)) :=
  (match g.body with
    | .fn _ _ b => Load.refs b
    | .const _ v => Load.refs v).filter fun (n, _, _) => (Prim.byName? n).isNone

structure St (T : List TypeDecl) where
  G : List Ty
  defs : Defs G
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
  let owner := if args.isEmpty then name else s!"{name}({", ".intercalate (args.map (showTy T))})"
  let elabAt (site : At → SiteId) : M T ((t : Ty) × Expr st.G [] t) := inGlobal c g.name do
    let cx : Cx T st.G := { site, σ, sigs := c.globals.map fun g => (g.name, g.sig), glob := st.glob }
    let ty (s : STy) : E Ty := match toTy T σ s with | .ok t => pure t | .error e => fail g.pos e
    match g.body with
    | .fn params ret b =>
      let tys ← params.mapM fun (_, _, s) => ty s
      let rt ← ty ret
      let pl : Scope := (params.map (·.2.1)).zip tys
      let ⟨bt, be⟩ ← elabExpr cx pl b
      let be ← coerce cx b.pos rt bt be
      let be ← castList (F := fun Γ => Expr st.G Γ rt) g.pos be (b := tys ++ [])
      pure (⟨.fn tys rt, .lam be⟩ : (t : Ty) × Expr st.G [] t)
    | .const s v =>
      let want ← ty s
      let ⟨vt, ve⟩ ← elabExpr cx [] v
      pure ⟨want, ← coerce cx v.pos want vt ve⟩
  -- A site's ordinal is its rank among the instance's sites in source order, so a first elaboration names each site
  -- by its position only to rank them.
  let key (p : At) : Nat := p.line * 2 ^ 32 + p.col
  let ⟨t, body⟩ ← elabAt fun p => ⟨owner, key p⟩
  let ranked := ((Expr.sites st.defs body).map (·.2.2.site.ordinal) ++
    (Expr.effectSites st.defs body).map (·.2.2.2.site.ordinal)).mergeSort.eraseDups
  let ⟨t, body⟩ ← if ranked.isEmpty then pure ⟨t, body⟩ else elabAt fun p => ⟨owner, ranked.idxOf (key p) + 1⟩
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

/-- The user types a field type names, after alias expansion. -/
partial def namedTypes : STy → List String
  | .con n args => n :: args.flatMap namedTypes
  | .fn ps r => ps.flatMap namedTypes ++ namedTypes r
  | .tuple ts => ts.flatMap namedTypes
  | .var _ | .hole _ => []

/-- The user types, each with its fields' types expanded. A type is elaborated after every type its fields name, so a
type that refers to itself, directly or through others, is refused: its values would be infinite trees. -/
def userTypes (fileOf : String → Option String) (types : List Surface.TypeDef) (aliases : List Surface.AliasDef) :
    Except LoadError (List TypeDecl) := do
  let names := prelude.map (·.name) ++ types.map (·.name) ++ aliases.map (·.name)
  if let some n := nodup names then throw ⟨none, none, s!"type {n} is declared twice or is built in"⟩
  let err (t : Surface.TypeDef) (msg : String) : LoadError := ⟨fileOf t.name, some t.pos, s!"{t.name}: {msg}"⟩
  let deps (t : Surface.TypeDef) : List String :=
    (t.variants.flatMap fun (_, fs) => fs.flatMap fun (_, s) => namedTypes s).filter fun n => types.any (·.name == n)
  -- Depth-first: `path` holds the types being visited, so meeting one again closes a cycle.
  let rec visit (fuel : Nat) (path : List String) (order : List String) (n : String) :
      Except LoadError (List String) := do
    let some t := types.find? (·.name == n) | return order
    if order.contains n then return order
    if path.contains n then
      throw (err t s!"refers to itself: {" -> ".intercalate ((path.reverse.dropWhile (· != n)) ++ [n])}")
    match fuel with
    | 0 => return order
    | fuel + 1 =>
      let order ← (deps t).foldlM (visit fuel (n :: path)) order
      return order ++ [n]
  let order ← types.foldlM (fun o t => visit (types.length + 1) [] o t.name) []
  let shells : List TypeDecl := prelude ++ types.map fun t => { name := t.name, params := t.params, variants := [] }
  let filled ← order.foldlM (init := shells) fun T n => do
    let some t := types.find? (·.name == n) | throw ⟨none, none, s!"internal: type {n}"⟩
    let some i := T.findIdx? (·.name == n) | throw ⟨none, none, s!"internal: type {n}"⟩
    if builtinName t.name || ownedByTazuna t.name then throw (err t "this type belongs to Lean")
    if let some p := nodup t.params then throw (err t s!"type parameter {p} is declared twice")
    if let some v := nodup (t.variants.map (·.1)) then throw (err t s!"variant {v} is declared twice")
    -- Gleam's naming rules give each variant its own atom; the canonical order (`Ty.ordered`) rests on it.
    if let some a := nodup (t.variants.map (atomName ·.1)) then
      throw (err t s!"two variants have the Erlang atom {a}")
    let σ := t.params.zipIdx.map fun (p, k) => (p, Ty.param k)
    let variants ← t.variants.mapM fun (v, fields) => do
      if let some l := nodup (fields.filterMap (·.1)) then throw (err t s!"{v} has the label {l} twice")
      let fields ← fields.mapM fun (l, s) => match toTy T σ s with
        | .ok ty => pure ({ label := l, ty } : Field)
        | .error e => throw (err t e)
      pure ({ name := v, fields } : Variant)
    pure (T.set i { name := t.name, params := t.params, variants })
  return filled.drop prelude.length

/-- Every alias must stand for a type, even one nothing uses: its parameters distinct, its body's type variables among
them, and its expansion free of cycles and well formed. -/
def checkAliases (fileOf : String → Option String) (T : List TypeDecl) (aliases : List Surface.AliasDef) :
    Except LoadError Unit :=
  aliases.forM fun a => do
    let err (msg : String) : LoadError := ⟨fileOf a.name, some a.pos, s!"{a.name}: {msg}"⟩
    if builtinName a.name || ownedByTazuna a.name then throw (err "this type belongs to Lean")
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

/-- The program the IR holds, its declarations by name: Gleam gives top-level declarations no order, so nothing the
engine prints or asks depends on the order the source writes them in. -/
def read (j : Lean.Json) : Except LoadError Surface.Program :=
  match Surface.readProgram (builtinAliases.map (·.1)) j with
  | .ok p => pure { p with
      types := p.types.mergeSort (·.name ≤ ·.name), aliases := p.aliases.mergeSort (·.name ≤ ·.name),
      functions := p.functions.mergeSort (·.name ≤ ·.name), constants := p.constants.mergeSort (·.name ≤ ·.name) }
  | .error e => throw ⟨none, e.pos, match e.global with | some g => s!"{g}: {e.message}" | none => e.message⟩

/-- A declaration of the IR without its positions (`at`), its local names (variables, parameters, names a pattern
binds) numbered in the order they first appear: a bijection within the declaration, so two declarations give the same
JSON exactly where they are equal up to positions and renaming locals. A parameter is an object in `params` (a type's
parameters are strings). -/
partial def declKey (param : Bool) : Lean.Json → StateM (Array String) Lean.Json
  | .obj kvs => do
    let tag (k : String) : String := match kvs.get? k with
      | some (.str t) => t
      | _ => ""
    let named := param || tag "op" == "var" || ["var", "discard", "as"].contains (tag "p")
    let mut out : List (String × Lean.Json) := []
    for (k, v) in kvs.toList do
      if k == "at" then continue
      let v' : Lean.Json ← match k, v with
        | "name", .str n => if named then numbered n else pure v
        | "params", .arr ps => Lean.Json.arr <$> ps.mapM (declKey true)
        | _, v => declKey false v
      out := out ++ [(k, v')]
    return Lean.Json.mkObj out
  | .arr a => Lean.Json.arr <$> a.mapM (declKey false)
  | j => pure j
where
  numbered (n : String) : StateM (Array String) Lean.Json := do
    let seen ← get
    match seen.idxOf? n with
    | some i => return .str s!"${i}"
    | none =>
      set (seen.push n)
      return .str s!"${seen.size}"

/-- What builds every question's script, for the direct keys (`Smt.directKey`): the IR without what only messages
read, its source files and each declaration's positions and local names (`declKey`), with its declarations by name as
`read` takes them, as reproducible builds map source paths away. So an edit that changes no meaning keeps every direct
key. -/
def scriptInputs (j : Lean.Json) : Lean.Json :=
  let byName (x : Lean.Json) : String := match x.getObjValAs? String "name" with
    | .ok n => n
    | .error _ => ""
  match j with
  | .obj kvs => Lean.Json.mkObj (kvs.foldl (fun acc k v => match k, v with
      | "sources", _ => acc
      | _, .arr a => acc ++ [(k, .arr ((a.map fun d => (declKey false d).run' #[]).qsort (byName · < byName ·)))]
      | _, v => acc ++ [(k, v)]) [])
  | j => j

/-- The model functions of the root module, by their names in it: functions that take nothing and return a
`tazuna.Model`. -/
def models (j : Lean.Json) : Except LoadError (List String) := do
  let p ← read j
  let module := moduleOf p.root
  return p.functions.filterMap fun f =>
    match f.params, f.ret with
    | [], .con "tazuna.Model" [] => if moduleOf f.name == module then (f.name.splitOn ".").getLast? else none
    | _, _ => none

/-- Loads the IR with the function `rootName` of the root module as its root, or the IR's own root where none is given,
which must be a function of type `rootTy` (the engine asks for `spec() -> tazuna.Spec` or a model function's
`fn() -> tazuna.Model`). -/
def load (rootTy : Ty) (j : Lean.Json) (rootName : Option String := none) : Except LoadError (Program rootTy) := do
  let p ← read j
  let p := match rootName with
    | some n => { p with root := moduleOf p.root ++ "." ++ n }
    | none => p
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
  -- Every global is elaborated at its own type variables so that unused code is checked too, but the program holds only
  -- the root and the instances it demands: a copy at type variables never runs, and its kept functions and handles
  -- would give the pending table and the layout types that have no value.
  let all : M T Unit := do
    for g in globals do
      demand c g.name (g.sig.tvars.zipIdx.map fun (_, k) => Ty.param k)
  discard <| all.run { G := [], defs := .nil, done := [] }
  unless root.sig.tvars.isEmpty && root.sig.labels.isSome do
    throw ⟨c.file root.name, some root.pos, s!"root {root.name} must be a function without type variables"⟩
  let ((), st) ← (demand c root.name [] : M T Unit).run { G := [], defs := .nil, done := [] }
  let some ⟨t, v⟩ := st.glob root.name [] | throw ⟨none, none, "internal: root not elaborated"⟩
  match Ty.same t rootTy with
  | some ⟨h⟩ => pure { types := T, globals := st.G, defs := st.defs, root := h ▸ v }
  | none => throw ⟨c.file root.name, some root.pos,
      s!"root {root.name} has type {showTy T t}; it must be {showTy T rootTy}"⟩

end Tazuna.Ir.Load
