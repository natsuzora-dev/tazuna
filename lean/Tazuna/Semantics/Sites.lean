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

mutual
theorem Ty_same_self : (t : Ty) → (Ty.same t t).isSome = true
  | .int | .str | .date | .id => rfl
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

/-- The senders a service's states can name. -/
def senderShapes (v : ServiceV) : List ((ks : List Ty) × SenderShape ks) :=
  v.machines.map (fun m => ⟨[m.key], .machine m.name m.key⟩) ++ v.reactions.map fun x => ⟨[], .reaction x.name⟩

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- Every shape of request a service's effects can make, given the program's sites: each external command or query
the service may request, and each site of the type its `on_answer` and `ensures` must have, whose fields are data. -/
def requestShapes (v : ServiceV) (sites : List AnySite) : List (RequestShape v.event) :=
  v.declared.flatMap fun (x, d) =>
    let mk (name : String) (i o : Ty) (j : Option Ty)
        (ens : Option ((Γ : List Ty) × Site Γ (Ty.fn [i, answerTy o j] Ty.rules))) : List (RequestShape v.event) :=
      (sitesOf sites (Ty.fn [answerTy o j] (.list v.event))).filterMap fun ⟨aΓ, a⟩ =>
        if h : (Ty.tuple [i, .tuple ((ens.map (·.1)).getD []), .tuple aΓ]).isData = true then
          some ⟨x, name, i, o, j, ens, aΓ, a, h⟩
        else none
    match d with
    | .externalCommand n i o j => mk n i o (some j) none
    | .externalQuery n i o _ => (sitesOf sites (Ty.fn [i, o] Ty.rules)).flatMap fun s => mk n i o none (some s)
    | _ => []

/-- Every shape of pending request a service can hold: each sender whose key is data, with each request shape. -/
def shapes (v : ServiceV) (sites : List AnySite) : List (PendingShape v.event) :=
  (senderShapes v).flatMap fun ⟨ks, snd⟩ =>
    if h : (Ty.tuple ks).isData = true then (requestShapes v sites).map fun r => { r with ks, sender := snd, hks := h }
    else []

/-- The type that codes a pending request of the shapes `shs`: one variant per shape, holding its fields. Its index
names no type of the program; the variants tell it apart. -/
def pendingEntry {e : Ty} (shs : List (PendingShape e)) : Ty := .adt 1000000 [] (shs.map PendingShape.fields)

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
