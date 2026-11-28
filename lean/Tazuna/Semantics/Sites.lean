import Tazuna.Semantics.Step

/-! The places a program writes kept functions, and the pending requests a state can hold. A kept function is a
closure record (`Fun`): a site's source with the values it captured. A pending request holds such records, so the
requests a program's states can hold are finitely many shapes: who sent it, which external command or query of the
service's `declared` it asks for, and which sites its `on_answer` and its query's `ensures` come from: the shape of
the effect that started it (`RequestShape`) with its sender. A shape's fields are the data that varies (the sender's key, the input, the captured values), so a pending request is a shape
with its fields (`PendingShape.pending`), the form a symbolic state holds it in. -/

namespace Tazuna.Ir

/-- Where a program writes a kept function: its source over the definitions before the global that holds it, with
the types `Γ` of the values it captures. With those values it is the closure record `Site.fn`. -/
structure Site (Γ : List Ty) (t : Ty) where
  site : SiteId
  G : List Ty
  defs : Defs G
  hΓ : (Ty.tuple Γ).isData = true
  ht : t.isData = true
  body : Expr G Γ t

abbrev AnySite := (Γ : List Ty) × (t : Ty) × Site Γ t

/-- The closure record of the site with the captured values `env`. -/
def Site.fn {Γ : List Ty} {t : Ty} (s : Site Γ t) (env : (Ty.tuple Γ).den0) : Fun t :=
  ⟨s.site, s.G, s.defs, Γ, env, s.hΓ, s.ht, s.body⟩

section
variable {G : List Ty} (D : Defs G)

mutual
/-- The kept functions an expression writes, nested ones included, each over the definitions `D`. -/
def Expr.sites {Γ : List Ty} {t : Ty} : Expr G Γ t → List AnySite
  | .int _ | .str _ | .var _ | .global _ | .prim .. => []
  | .ctor _ es | .tuple es => Exprs.sites es
  | .field _ _ _ e | .index e _ | .not e | .neg e | .lam e => Expr.sites e
  | .update e p => Expr.sites e ++ Patch.sites p
  | .call f args => Expr.sites f ++ Exprs.sites args
  | .let_ e body | .bin _ e body => Expr.sites e ++ Expr.sites body
  | .case e cs _ => Expr.sites e ++ Clauses.sites cs
  | .list items => Items.sites items
  | @Expr.close _ _ Γ' t' site env hΓ ht body => ⟨Γ', t', ⟨site, G, D, hΓ, ht, body⟩⟩ :: Exprs.sites env ++ Expr.sites body
  | .closeEffect _ env _ _ body => Exprs.sites env ++ Expr.sites body
def Exprs.sites {Γ ts : List Ty} : Exprs G Γ ts → List AnySite
  | .nil => []
  | .cons e es => Expr.sites e ++ Exprs.sites es
def Items.sites {Γ : List Ty} {t : Ty} : Items G Γ t → List AnySite
  | .nil => []
  | .cons e es => Expr.sites e ++ Items.sites es
def Patch.sites {Γ ts : List Ty} : Patch G Γ ts → List AnySite
  | .nil => []
  | .keep rest => Patch.sites rest
  | .set e rest => Expr.sites e ++ Patch.sites rest
def Clauses.sites {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List AnySite
  | .nil => []
  | .cons _ body rest => Expr.sites body ++ Clauses.sites rest
  | .guarded _ g body rest => Expr.sites g ++ Expr.sites body ++ Clauses.sites rest
end

end

/-- Every kept function a program writes: each global's, over the definitions before it, as `Defs.eval` evaluates
it. -/
def Defs.sites : {G : List Ty} → Defs G → List AnySite
  | [], .nil => []
  | _ :: _, .snoc defs _ body => defs.sites ++ body.sites defs

/-- Where a program writes a kept function that returns effects (`Expr.closeEffect`): like a site, but what it returns
holds effects, so it is no site a pending request or code names; its records are `EffectFun`s. -/
structure EffectSite (Γ ps : List Ty) (r : Ty) where
  site : SiteId
  G : List Ty
  defs : Defs G
  hΓ : (Ty.tuple Γ).isData = true
  hps : (Ty.tuple ps).isData = true
  body : Expr G Γ (.fn ps r)

abbrev AnyEffectSite := (Γ : List Ty) × (ps : List Ty) × (r : Ty) × EffectSite Γ ps r

section
variable {G : List Ty} (D : Defs G)

mutual
/-- The kept functions returning effects an expression writes, nested ones included, each over the definitions `D`. -/
def Expr.effectSites {Γ : List Ty} {t : Ty} : Expr G Γ t → List AnyEffectSite
  | .int _ | .str _ | .var _ | .global _ | .prim .. => []
  | .ctor _ es | .tuple es => Exprs.effectSites es
  | .field _ _ _ e | .index e _ | .not e | .neg e | .lam e => Expr.effectSites e
  | .update e p => Expr.effectSites e ++ Patch.effectSites p
  | .call f args => Expr.effectSites f ++ Exprs.effectSites args
  | .let_ e body | .bin _ e body => Expr.effectSites e ++ Expr.effectSites body
  | .case e cs _ => Expr.effectSites e ++ Clauses.effectSites cs
  | .list items => Items.effectSites items
  | .close _ env _ _ body => Exprs.effectSites env ++ Expr.effectSites body
  | @Expr.closeEffect _ _ Γ' ps r site env hΓ hps body =>
    ⟨Γ', ps, r, ⟨site, G, D, hΓ, hps, body⟩⟩ :: Exprs.effectSites env ++ Expr.effectSites body
def Exprs.effectSites {Γ ts : List Ty} : Exprs G Γ ts → List AnyEffectSite
  | .nil => []
  | .cons e es => Expr.effectSites e ++ Exprs.effectSites es
def Items.effectSites {Γ : List Ty} {t : Ty} : Items G Γ t → List AnyEffectSite
  | .nil => []
  | .cons e es => Expr.effectSites e ++ Items.effectSites es
def Patch.effectSites {Γ ts : List Ty} : Patch G Γ ts → List AnyEffectSite
  | .nil => []
  | .keep rest => Patch.effectSites rest
  | .set e rest => Expr.effectSites e ++ Patch.effectSites rest
def Clauses.effectSites {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List AnyEffectSite
  | .nil => []
  | .cons _ body rest => Expr.effectSites body ++ Clauses.effectSites rest
  | .guarded _ g body rest => Expr.effectSites g ++ Expr.effectSites body ++ Clauses.effectSites rest
end

end

def Defs.effectSites : {G : List Ty} → Defs G → List AnyEffectSite
  | [], .nil => []
  | _ :: _, .snoc defs _ body => defs.effectSites ++ body.effectSites defs

section
variable {G : List Ty}

mutual
/-- The globals an expression reads, by position from the innermost, nested functions included. -/
def Expr.globals {Γ : List Ty} {t : Ty} : Expr G Γ t → List Nat
  | .int _ | .str _ | .var _ | .prim .. => []
  | .global v => [v.idx]
  | .ctor _ es | .tuple es => Exprs.globals es
  | .field _ _ _ e | .index e _ | .not e | .neg e | .lam e => Expr.globals e
  | .update e p => Expr.globals e ++ Patch.globals p
  | .call f args => Expr.globals f ++ Exprs.globals args
  | .let_ e body | .bin _ e body => Expr.globals e ++ Expr.globals body
  | .case e cs _ => Expr.globals e ++ Clauses.globals cs
  | .list items => Items.globals items
  | .close _ env _ _ body | .closeEffect _ env _ _ body => Exprs.globals env ++ Expr.globals body
def Exprs.globals {Γ ts : List Ty} : Exprs G Γ ts → List Nat
  | .nil => []
  | .cons e es => Expr.globals e ++ Exprs.globals es
def Items.globals {Γ : List Ty} {t : Ty} : Items G Γ t → List Nat
  | .nil => []
  | .cons e es => Expr.globals e ++ Items.globals es
def Patch.globals {Γ ts : List Ty} : Patch G Γ ts → List Nat
  | .nil => []
  | .keep rest => Patch.globals rest
  | .set e rest => Expr.globals e ++ Patch.globals rest
def Clauses.globals {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List Nat
  | .nil => []
  | .cons _ body rest => Expr.globals body ++ Clauses.globals rest
  | .guarded _ g body rest => Expr.globals g ++ Expr.globals body ++ Clauses.globals rest
end

end

/-- What an expression collects of its own source (`f`), its sites or its handles, over the definitions `D`. -/
abbrev Collect (α : Type) := {G Γ : List Ty} → {t : Ty} → Defs G → Expr G Γ t → List α

-- A global's position is below the table's length, so the empty list is never read.
set_option linter.tazuna.silentDefault false in
/-- What `f` collects of an expression and, by the table `tbl` of each global's, of every global it reads. -/
def Expr.usesWith {α : Type} (f : Collect α) {G Γ : List Ty} {t : Ty} (D : Defs G) (tbl : List (List α))
    (e : Expr G Γ t) : List α :=
  f D e ++ e.globals.flatMap fun i => tbl.getD i []

/-- For each global, innermost first, what `f` collects of it and of every global it reads, transitively: the kept
functions or handles its value can hold or make. -/
def Defs.uses {α : Type} (f : Collect α) : {G : List Ty} → Defs G → List (List α)
  | [], .nil => []
  | _ :: _, .snoc defs _ body => body.usesWith f defs (defs.uses f) :: defs.uses f

-- A global's position is below the table's length, so the empty list is never read.
set_option linter.tazuna.silentDefault false in
/-- What `f` collects of the global at position `i` and of every global it reads. -/
def Defs.usesAt {α : Type} (f : Collect α) {G : List Ty} (D : Defs G) (i : Nat) : List α := (D.uses f).getD i []

/-- What `f` collects of an expression and of every global it reads, transitively. -/
def Expr.uses {α : Type} (f : Collect α) {G Γ : List Ty} {t : Ty} (D : Defs G) (e : Expr G Γ t) : List α :=
  e.usesWith f D (D.uses f)

/-- What `f` collects of every global. -/
def Defs.collect {α : Type} (f : Collect α) : {G : List Ty} → Defs G → List α
  | [], .nil => []
  | _ :: _, .snoc defs _ body => defs.collect f ++ f defs body

/-- The kept functions an expression writes. -/
def sitesC : Collect AnySite := fun D e => e.sites D

/-- The handles an expression makes. -/
def handlesC : Collect HandleSite := fun _ e => e.handles

/-- An own command or query a call sends: the handles its first argument can make, when that argument calls a global
with no arguments (`none`: any of the function's), and the site of its `on_answer`, when written in place (`none`: any
of its type). The encoder codes a send by the handle's name and that site, so these bound its own kinds. -/
structure SendSite where
  handles : Option (List HandleSite)
  site : Option SiteId

/-- The global a call of no arguments calls. -/
def Expr.globalCall? {G Γ : List Ty} {t : Ty} : Expr G Γ t → Option Nat
  | .call (.global v) .nil => some v.idx
  | _ => none

/-- The site of a kept function written in place. -/
def Expr.closeSite? {G Γ : List Ty} {t : Ty} : Expr G Γ t → Option SiteId
  | .close site .. => some site
  | _ => none

/-- The global the `k`th expression calls with no arguments. -/
def Exprs.globalCallAt? {G Γ : List Ty} : {ts : List Ty} → Exprs G Γ ts → Nat → Option Nat
  | _, .nil, _ => none
  | _, .cons e _, 0 => e.globalCall?
  | _, .cons _ es, k + 1 => es.globalCallAt? k

/-- The site of the `k`th expression, a kept function written in place. -/
def Exprs.closeSiteAt? {G Γ : List Ty} : {ts : List Ty} → Exprs G Γ ts → Nat → Option SiteId
  | _, .nil, _ => none
  | _, .cons e _, 0 => e.closeSite?
  | _, .cons _ es, k + 1 => es.closeSiteAt? k

def Prim.sends : Prim → Bool
  | .sendCommand | .sendQuery => true
  | _ => false

/-- Whether the function is `send_command` or `send_query`. -/
def sendPrim {G Γ ps : List Ty} {r : Ty} (f : Expr G Γ (.fn ps r)) : Bool :=
  match f with
  | .prim p _ _ => p.sends
  | _ => false

/-- What a call sends, when it calls `send_command` or `send_query`: the command or query is its first argument, the
`on_answer` its third. -/
def sendAt {G Γ ps : List Ty} {r : Ty} (D : Defs G) (f : Expr G Γ (.fn ps r)) (args : Exprs G Γ ps) :
    Option SendSite :=
  if sendPrim f then some ⟨(args.globalCallAt? 0).map (D.usesAt handlesC), args.closeSiteAt? 2⟩ else none

section
variable {G : List Ty} (D : Defs G)

mutual
/-- The own commands and queries an expression sends, nested functions included. A send built-in passed as a value
sends whatever its caller gives it. -/
def Expr.sends {Γ : List Ty} {t : Ty} : Expr G Γ t → List SendSite
  | .int _ | .str _ | .var _ | .global _ => []
  | .prim p _ _ => if p.sends then [⟨none, none⟩] else []
  | .ctor _ es | .tuple es => Exprs.sends es
  | .field _ _ _ e | .index e _ | .not e | .neg e | .lam e => Expr.sends e
  | .update e p => Expr.sends e ++ Patch.sends p
  | .call f args => match sendAt D f args with
    | some w => w :: Exprs.sends args
    | none => Expr.sends f ++ Exprs.sends args
  | .let_ e body | .bin _ e body => Expr.sends e ++ Expr.sends body
  | .case e cs _ => Expr.sends e ++ Clauses.sends cs
  | .list items => Items.sends items
  | .close _ env _ _ body | .closeEffect _ env _ _ body => Exprs.sends env ++ Expr.sends body
def Exprs.sends {Γ ts : List Ty} : Exprs G Γ ts → List SendSite
  | .nil => []
  | .cons e es => Expr.sends e ++ Exprs.sends es
def Items.sends {Γ : List Ty} {t : Ty} : Items G Γ t → List SendSite
  | .nil => []
  | .cons e es => Expr.sends e ++ Items.sends es
def Patch.sends {Γ ts : List Ty} : Patch G Γ ts → List SendSite
  | .nil => []
  | .keep rest => Patch.sends rest
  | .set e rest => Expr.sends e ++ Patch.sends rest
def Clauses.sends {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List SendSite
  | .nil => []
  | .cons _ body rest => Expr.sends body ++ Clauses.sends rest
  | .guarded _ g body rest => Expr.sends g ++ Expr.sends body ++ Clauses.sends rest
end

end

/-- The own commands and queries an expression sends. -/
def sendsC : Collect SendSite := fun D e => e.sends D

theorem Defs.uses_sub {α : Type} (f : Collect α) : {G : List Ty} → (D : Defs G) → (i : Nat) →
    ∀ x ∈ D.usesAt f i, x ∈ D.collect f
  | [], .nil, _, x, h => by simp [Defs.usesAt, Defs.uses] at h
  | _ :: _, .snoc defs _ body, 0, x, h => by
    simp only [Defs.usesAt, Defs.uses, List.getD_cons_zero, Expr.usesWith, List.mem_append, List.mem_flatMap] at h
    simp only [Defs.collect, List.mem_append]
    rcases h with h | ⟨j, -, h⟩
    · exact .inr h
    · exact .inl (Defs.uses_sub f defs j x h)
  | _ :: _, .snoc defs _ _, i + 1, x, h => by
    simp only [Defs.usesAt, Defs.uses, List.getD_cons_succ] at h
    simp only [Defs.collect, List.mem_append]
    exact .inl (Defs.uses_sub f defs i x h)

theorem Defs.collect_sites : {G : List Ty} → (D : Defs G) → D.collect sitesC = D.sites
  | [], .nil => rfl
  | _ :: _, .snoc defs _ _ => by simp only [Defs.collect, Defs.sites, Defs.collect_sites defs]; rfl

theorem Defs.collect_handles : {G : List Ty} → (D : Defs G) → D.collect handlesC = D.handles
  | [], .nil => rfl
  | _ :: _, .snoc defs _ _ => by simp only [Defs.collect, Defs.handles, Defs.collect_handles defs]; rfl

mutual
theorem Ty_same_self : (t : Ty) → (Ty.same t t).isSome = true
  | .int | .str | .id => rfl
  | .point _ => by simp [Ty.same]
  | .param i => by simp [Ty.same]
  | .list a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self a); simp [Ty.same, e]
  | .bag a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self a); simp [Ty.same, e]
  | .tuple a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a); simp [Ty.same, e]
  | .fn a r => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_same_self r)
    simp [Ty.same, e, e']
  | .adt i a v => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_samess_self v)
    simp [Ty.same, e, e']
  | .table k v => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self k)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_same_self v)
    simp [Ty.same, e, e']
  | .dsl k a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a); simp [Ty.same, e]
theorem Ty_sames_self : (ts : List Ty) → (Ty.sames ts ts).isSome = true
  | [] => rfl
  | t :: ts => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self t)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_sames_self ts)
    simp [Ty.sames, e, e']
theorem Ty_samess_self : (vs : List (List Ty)) → (Ty.samess vs vs).isSome = true
  | [] => rfl
  | ts :: vs => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self ts)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_samess_self vs)
    simp [Ty.samess, e, e']
end

theorem Ty_same_rfl (t : Ty) : Ty.same t t = some ⟨rfl⟩ := by
  obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self t); rw [e]

/-- The sites of the type `t`. -/
def sitesOf (sites : List AnySite) (t : Ty) : List ((Γ : List Ty) × Site Γ t) :=
  sites.filterMap fun ⟨Γ, u, s⟩ => (Ty.same u t).map fun ⟨h⟩ => ⟨Γ, h ▸ s⟩

/-- What sent a pending request, with the types of what varies: a machine's instance by its key, or a reaction. -/
inductive SenderShape : List Ty → Type where
  | machine (name : String) (key : Ty) : SenderShape [key]
  | reaction (name : String) : SenderShape []

def SenderShape.sender : {ks : List Ty} → SenderShape ks → (Ty.tuple ks).den0 → Sender
  | _, .machine n k, (key, ()) => .machine n ⟨k, key⟩
  | _, .reaction n, () => .reaction n

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- One shape of request an effect makes: the external command or query of the service's `declared` it asks for,
and the sites of its `on_answer` and, for a query, of its `ensures`. -/
structure RequestShape (e : Ty) where
  external : String
  name : String
  input : Ty
  output : Ty
  rejection : Option Ty
  /-- A query's `ensures`, with the types of the values it captured; a command has none. -/
  ensures : Option ((Γ : List Ty) × Site Γ (Ty.fn [input, answerTy output rejection] Ty.rules))
  answerΓ : List Ty
  onAnswer : Site answerΓ (Ty.fn [answerTy output rejection] (.list e))
  /-- What varies, each value data: the input, and the values each site captured. -/
  hfields : (Ty.tuple [input, .tuple ((ensures.map (·.1)).getD []), .tuple answerΓ]).isData = true

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- The types of the values the `ensures` captured; none without one. -/
def RequestShape.ensuresΓ {e : Ty} (sh : RequestShape e) : List Ty := (sh.ensures.map (·.1)).getD []

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- The `ensures` closure record with the captured values `env`. -/
def ensuresFn {t : Ty} : (ens : Option ((Γ : List Ty) × Site Γ t)) → (Ty.tuple ((ens.map (·.1)).getD [])).den0 →
    Option (Fun t)
  | none, _ => none
  | some ⟨_, s⟩, env => some (s.fn env)

/-- The types of what varies among the requests of a shape, as an effect value holds them. -/
def RequestShape.fields {e : Ty} (sh : RequestShape e) : List Ty := [sh.input, .tuple sh.ensuresΓ, .tuple sh.answerΓ]

/-- One shape of pending request: an effect's request shape with its sender. -/
structure PendingShape (e : Ty) extends RequestShape e where
  ks : List Ty
  sender : SenderShape ks
  hks : (Ty.tuple ks).isData = true

/-- The types of what varies among the requests of a shape: the sender's key, then the request's fields. -/
def PendingShape.fields {e : Ty} (sh : PendingShape e) : List Ty := .tuple sh.ks :: sh.toRequestShape.fields

theorem PendingShape.hdata {e : Ty} (sh : PendingShape e) : (Ty.tuple sh.fields).isData = true := by
  have h1 := sh.hks; have h2 := sh.hfields
  simp only [PendingShape.fields, RequestShape.fields, Ty.isData, Ty.isDatas, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- The pending request of the shape with the wire id `id` and the fields `x`. -/
def PendingShape.pending {e : Ty} (sh : PendingShape e) (id : Nat) (x : Ty.dens sh.fields) : Step.Pending e :=
  let y := Ty.down (.tuple sh.fields) sh.hdata x
  ⟨id, sh.sender.sender y.1, sh.external,
    { name := sh.name, input := sh.input, output := sh.output, rejection := sh.rejection, value := y.2.1,
      ensures := ensuresFn sh.ensures y.2.2.1, onAnswer := sh.onAnswer.fn y.2.2.2.1 }⟩

/-- The kept functions an effect function's source and the globals it reads write: all its effects can hold. -/
def EffectFun.usedSites {ps : List Ty} {r : Ty} (f : EffectFun ps r) : List AnySite := f.body.uses sitesC f.defs

/-- What a function of the step and the globals it reads write: kept functions, handles and sends. -/
abbrev Uses := List AnySite × List HandleSite × List SendSite

/-- The kept functions, handles and sends a kept function's source and the globals it reads write. -/
def Fun.uses {t : Ty} (f : Fun t) : Uses :=
  (f.body.uses sitesC f.defs, f.body.uses handlesC f.defs, f.body.uses sendsC f.defs)

/-- The kept functions, handles and sends a kept function that returns effects, and the globals it reads, write. -/
def EffectFun.uses {ps : List Ty} {r : Ty} (f : EffectFun ps r) : Uses :=
  (f.usedSites, f.body.uses handlesC f.defs, f.body.uses sendsC f.defs)

/-- What each function a step of the service runs, each response function a run's goal applies and each create's
table function uses: every kept function of the service (`rootUses_eq`). A site such a function uses (a pending
request's `on_answer`, an own command's) uses no more (`Expr.uses_closed`), so these are all the codes a script
meets. -/
def rootUses (v : ServiceV) : List Uses :=
  [v.apply.uses, v.invariants.uses] ++
    v.commands.flatMap (fun x => [x.accepts.uses, x.decide.uses, x.ensures.uses]) ++
    v.queries.flatMap (fun q => [q.accepts.uses, q.resolve.uses]) ++
    v.machines.flatMap (fun m => [m.instances.uses, m.on.uses, m.timer.uses, m.invariants.uses, m.effect.uses]) ++
    v.reactions.map (·.react.uses) ++ v.subscribes.map (·.wrap.uses) ++
    v.responses.flatMap (fun r => [r.after.uses, r.then_.uses, r.deadline.uses])

/-- Every kept function of a service, by field. Each structure is matched whole, so a field added to one of them stops
this from compiling until it is listed or matched as `_`; `rootUses_eq` then holds only once `rootUses` reads it too.
`_` marks a field that holds no function a script runs: data, names and types; `declares` and `declared` hold the
commands and queries the service lists and the externals' declarations, whose functions a step reaches through the
program's sites; `scenarios` run in `test` alone. -/
def keptUses : ServiceV → List Uses
  | ⟨_name, _records, _event, _caller, _init, apply, subscribes, _declares, commands, queries, _sources, machines,
      reactions, invariants, responses, _cascade, _scenarios, _declared⟩ =>
    [apply.uses, invariants.uses] ++
      commands.flatMap (fun (⟨_name, _input, _rejection, _callers, accepts, decide, ensures⟩ : CommandV _records _event _caller) =>
        [accepts.uses, decide.uses, ensures.uses]) ++
      queries.flatMap (fun (⟨_name, _input, _output, _callers, accepts, resolve⟩ : QueryV _records _caller) =>
        [accepts.uses, resolve.uses]) ++
      machines.flatMap (fun (⟨_name, _key, _state, instances, _initial, on, timer, effect, invariants⟩ :
          MachineV _records _event) =>
        [instances.uses, on.uses, timer.uses, invariants.uses, effect.uses]) ++
      reactions.map (fun (⟨_name, react⟩ : ReactionV _records _event) => react.uses) ++
      subscribes.map (fun (⟨_source, _name, _sourceEvent, wrap⟩ : SubscriptionV _event) => wrap.uses) ++
      responses.flatMap (fun (⟨_name, after, then_, _within, deadline⟩ : ResponseV _records _event) =>
        [after.uses, then_.uses, deadline.uses])

/-- `rootUses` reads every kept function of the service. -/
theorem rootUses_eq (v : ServiceV) : rootUses v = keptUses v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := v
  rfl

/-- The handles of `H` a send can make. -/
def SendSite.handlesIn (w : SendSite) (H : List HandleSite) : List HandleSite :=
  match w.handles with
  | some hs => hs
  | none => H

/-- The sends a function of the step can run: its own, and those of each kept function it uses, which run when an
answer or an own command's result reaches it. -/
def rootSends (r : Uses) : List SendSite :=
  r.2.2 ++ r.1.flatMap fun s => s.2.2.body.uses sendsC s.2.2.defs

/-- The handles the service's own sends can name: each send's own, or for a send whose handle is no global called in
place, every handle of the function it is in. Every own effect of the service names one of these. -/
def ServiceV.sentHandles (v : ServiceV) : List HandleSite :=
  (rootUses v).flatMap fun r => (rootSends r).flatMap (·.handlesIn r.2.1)

/-- The handles the service's own sends name for certain: each send whose handle is a global called in place that
makes exactly one handle. -/
def ServiceV.definiteSends (v : ServiceV) : List HandleSite :=
  (rootUses v).flatMap fun r => (rootSends r).filterMap fun w => match w.handles with
    | some [h] => some h
    | _ => none

/-- Whether a handle names the command, by the name and types an own effect of it carries. -/
def _root_.Tazuna.Ir.CommandV.namedBy {r e c : Ty} (x : CommandV r e c) (h : HandleSite) : Bool :=
  h.kind == "command" && h.name == some x.name && match h.types with
    | [_, _, _, i, j] => (Ty.same i x.input).isSome && (Ty.same j x.rejection).isSome
    | _ => false

/-- Whether a handle names the query, by the name and types an own effect of it carries. -/
def _root_.Tazuna.Ir.QueryV.namedBy {r c : Ty} (x : QueryV r c) (h : HandleSite) : Bool :=
  h.kind == "query" && h.name == some x.name && match h.types with
    | [_, _, i, o] => (Ty.same i x.input).isSome && (Ty.same o x.output).isSome
    | _ => false

/-- The findings of `Illegal.callers` for a service: `Own` listed exactly when one of its sends may name the request,
read on `sentHandles` (every handle a send may name, so a request it lacks is never sent) and `definiteSends` (the
handles a send names for certain). -/
def ServiceV.callerRules (v : ServiceV) : List (Illegal × String) :=
  let rule (kind name : String) (callers : List (Ty.origin v.caller).den0) (named : HandleSite → Bool) :=
    let own := callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 Step.own)
    if callers.isEmpty then
      [(Illegal.callers, s!"{v.name}.{name}: callers is empty, so nothing may run the {kind}; list Outside for each outside caller that may send it, and Own if the service sends it")]
    else if own && !v.sentHandles.any named then
      [(Illegal.callers, s!"{v.name}.{name} lists Own, but nothing in {v.name} sends it; remove Own")]
    else if !own && v.definiteSends.any named then
      [(Illegal.callers, s!"{v.name} sends the {kind} {name}, whose callers lack Own; add Own to its callers")]
    else []
  v.commands.flatMap (fun x => rule "command" x.name x.callers x.namedBy) ++
    v.queries.flatMap fun q => rule "query" q.name q.callers q.namedBy

/-- The senders a service's states can name, each with the kept functions its requests can hold: a machine's
instance by its key, or a reaction, with the sites its effect function can reach. -/
def senderShapes (v : ServiceV) : List ((ks : List Ty) × SenderShape ks × List AnySite) :=
  v.machines.map (fun m => ⟨[m.key], .machine m.name m.key, m.effect.usedSites⟩) ++
    v.reactions.map fun x => ⟨[], .reaction x.name, x.react.usedSites⟩

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- Every shape of request the effects of the event type `e` can make, given the program's sites: each external
command or query `declared` lists, and each site of the type its `on_answer` and `ensures` must have, whose fields
are data. -/
def requestShapesAt (declared : List (String × DeclaredV)) (e : Ty) (sites : List AnySite) : List (RequestShape e) :=
  declared.flatMap fun (x, d) =>
    let mk (name : String) (i o : Ty) (j : Option Ty)
        (ens : Option ((Γ : List Ty) × Site Γ (Ty.fn [i, answerTy o j] Ty.rules))) : List (RequestShape e) :=
      (sitesOf sites (Ty.fn [answerTy o j] (.list e))).filterMap fun ⟨aΓ, a⟩ =>
        if h : (Ty.tuple [i, .tuple ((ens.map (·.1)).getD []), .tuple aΓ]).isData = true then
          some ⟨x, name, i, o, j, ens, aΓ, a, h⟩
        else none
    match d with
    | .externalCommand n i o j => mk n i o (some j) none
    | .externalQuery n i o _ => (sitesOf sites (Ty.fn [i, o] Ty.rules)).flatMap fun s => mk n i o none (some s)
    | _ => []

/-- Every shape of request a service's effects can make, given the program's sites. -/
def requestShapes (v : ServiceV) (sites : List AnySite) : List (RequestShape v.event) :=
  requestShapesAt v.declared v.event sites

/-- Every shape of pending request a service can hold: each sender whose key is data, with each request shape of the
sites it can reach. -/
def shapes (v : ServiceV) : List (PendingShape v.event) :=
  (senderShapes v).flatMap fun ⟨ks, snd, sites⟩ =>
    if h : (Ty.tuple ks).isData = true then (requestShapes v sites).map fun r => { r with ks, sender := snd, hks := h }
    else []

/-- The type that codes a pending request of the shapes `shs`: one variant per shape, holding its fields. Its index
names no type of the program; the variants tell it apart. -/
def pendingEntry {e : Ty} (shs : List (PendingShape e)) : Ty := .adt 1000000 [] (shs.map PendingShape.fields)

theorem pendingEntry_data {e : Ty} (shs : List (PendingShape e)) : (pendingEntry shs).isData = true := by
  induction shs with
  | nil => rfl
  | cons sh shs ih =>
    have h := sh.hdata
    simp only [pendingEntry, Ty.isData, List.map_cons, Ty.isDatass, Bool.and_eq_true] at ih h ⊢
    exact ⟨h, ih⟩

/-- The table type that codes pending requests of the shapes: wire ids to entries. Wire ids are naturals, as the
fresh counter's values are, so the keys have the counter's type. -/
def pendingTable {e : Ty} (shs : List (PendingShape e)) : Ty := .table (.dsl .fresh []) (pendingEntry shs)

/-- The pending request a value of `pendingEntry shs` codes, with the wire id `id`. -/
def pendingOf {e : Ty} : (shs : List (PendingShape e)) → Nat → Ty.alts (shs.map PendingShape.fields) → Step.Pending e
  | sh :: _, id, .inl x => sh.pending id x
  | _ :: shs, id, .inr y => pendingOf shs id y

theorem pendingOf_id {e : Ty} : (shs : List (PendingShape e)) → (id : Nat) → (x : Ty.alts (shs.map PendingShape.fields)) →
    (pendingOf shs id x).id = id
  | _ :: _, _, .inl _ => rfl
  | _ :: shs, id, .inr y => pendingOf_id shs id y

section
variable {e : Ty}

/-- The value of the pending entry type for the shape `sh` at index `j`, with the fields `fx`. -/
def pendingInj : (shs : List (PendingShape e)) → (j : Nat) → {sh : PendingShape e} → shs[j]? = some sh →
    Ty.dens sh.fields → Ty.alts (shs.map PendingShape.fields)
  | _ :: _, 0, _, h, fx => .inl ((Option.some.inj h).symm ▸ fx)
  | _ :: shs, j + 1, _, h, fx => .inr (pendingInj shs j h fx)

theorem pendingOf_inj (id : Nat) : (shs : List (PendingShape e)) → (j : Nat) → {sh : PendingShape e} →
    (h : shs[j]? = some sh) → (fx : Ty.dens sh.fields) → pendingOf shs id (pendingInj shs j h fx) = sh.pending id fx
  | s :: _, 0, sh, h, fx => by
    obtain rfl : s = sh := Option.some.inj h
    rfl
  | _ :: shs, j + 1, _, h, fx => pendingOf_inj id shs j h fx

end

/-- A pending request is of one of the shapes: some value of the shapes' entry type codes it. -/
def AtShapes {e : Ty} (shs : List (PendingShape e)) (p : Step.Pending e) : Prop :=
  ∃ x, pendingOf shs p.id x = p

end Tazuna.Ir
