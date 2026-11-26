import Tazuna.Semantics.Sites
import Tazuna.Semantics.Eval

/-! Every kept function a program builds is one of the program's sites: a closure record whose site, definitions and
source are the site's, with the values it captured (the label invariant of defunctionalization). `Reach P E t x`
says that every kept function the value `x` holds, or a function value returns, is such a record of the sites `P`, or
of the effect sites `E` when it returns effects; data holds none. `Expr.reach` proves evaluation keeps it, so with
unique site ids a closure's id fixes its source, and a record's source is covered wherever its site is. -/

namespace Tazuna.Ir

/-- No two sites share an id. The elaborator names each site by its module, position and the global instance that
holds it, and `check` refuses a program where two coincide. -/
def SitesUnique (P : List AnySite) : Prop := (P.map (·.2.2.site)).Nodup

instance (P : List AnySite) : Decidable (SitesUnique P) := inferInstanceAs (Decidable (List.Nodup _))

theorem nodup_map_inj {α β : Type} (f : α → β) : (l : List α) → (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
    f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: xs, h, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (e ▸ List.mem_map_of_mem hb') h.1
    · subst hb'; exact absurd (e.symm ▸ List.mem_map_of_mem ha') h.1
    · exact nodup_map_inj f xs h.2 ha' hb' e

/-- Among unique sites, the id fixes the site. -/
theorem site_eq {P : List AnySite} (hP : SitesUnique P) {a b : AnySite} (ha : a ∈ P) (hb : b ∈ P)
    (h : a.2.2.site = b.2.2.site) : a = b :=
  nodup_map_inj _ P hP ha hb h

section
variable (P : List AnySite) (E : List AnyEffectSite)

/-- The site record of a kept function. -/
def Fun.asSite {t : Ty} (f : Fun t) : AnySite := ⟨f.Γ, t, ⟨f.site, f.G, f.defs, f.hΓ, f.ht, f.body⟩⟩

/-- The effect site record of a kept function that returns effects. -/
def EffectFun.asSite {ps : List Ty} {r : Ty} (f : EffectFun ps r) : AnyEffectSite :=
  ⟨f.Γ, ps, r, ⟨f.site, f.G, f.defs, f.hΓ, f.hps, f.body⟩⟩

/-- A kept function that returns effects is a record of `E`, its source and the globals it reads write only sites of
`P`, and its source and definitions only effect sites of `E`. -/
structure EffectFun.Reach {ps : List Ty} {r : Ty} (f : EffectFun ps r) : Prop where
  site : f.asSite ∈ E
  /-- The kept functions its source writes and those of every global it reads, transitively. -/
  used : ∀ s ∈ f.usedSites, s ∈ P
  effectSites : ∀ s ∈ f.body.effectSites f.defs, s ∈ E
  defsEffectSites : ∀ s ∈ f.defs.effectSites, s ∈ E

/-- An effect's kept functions are records of `P`. -/
def EffectV.Reach {e : Ty} : EffectV e → Prop
  | .request r => r.onAnswer.asSite ∈ P ∧ (∀ f ∈ r.ensures, f.asSite ∈ P) ∧ r.input.isData = true ∧
      r.rejection.isSome = r.ensures.isNone
  | .command _ _ _ _ _ _ onAnswer => onAnswer.asSite ∈ P
  | .query _ _ _ _ _ _ onAnswer => onAnswer.asSite ∈ P

structure CommandV.Reach {r e c : Ty} (x : CommandV r e c) : Prop where
  accepts : x.accepts.asSite ∈ P
  decide : x.decide.asSite ∈ P
  ensures : x.ensures.asSite ∈ P

structure QueryV.Reach {r c : Ty} (x : QueryV r c) : Prop where
  accepts : x.accepts.asSite ∈ P
  resolve : x.resolve.asSite ∈ P

def DeclaredV.Reach : DeclaredV → Prop
  | .command _ _ _ x => x.Reach P
  | .query _ _ x => x.Reach P
  | _ => True

structure MachineV.Reach {r e : Ty} (m : MachineV r e) : Prop where
  effect : m.effect.Reach P E
  instances : m.instances.asSite ∈ P
  on : m.on.asSite ∈ P
  after : m.after.asSite ∈ P
  invariants : m.invariants.asSite ∈ P

def ReactionV.Reach {r e : Ty} (x : ReactionV r e) : Prop := x.react.Reach P E

/-- Every function the service keeps is a record of `P` or `E`. -/
structure ServiceV.Reach (v : ServiceV) : Prop where
  machines : ∀ m ∈ v.machines, m.Reach P E
  reactions : ∀ x ∈ v.reactions, x.Reach P E
  apply : v.apply.asSite ∈ P
  invariants : v.invariants.asSite ∈ P
  commands : ∀ x ∈ v.commands, x.Reach P
  queries : ∀ x ∈ v.queries, x.Reach P
  subscribes : ∀ x ∈ v.subscribes, x.wrap.asSite ∈ P
  responses : ∀ r ∈ v.responses, r.after.asSite ∈ P ∧ r.then_.asSite ∈ P
  creates : ∀ x ∈ v.bounds.creates, x.table.asSite ∈ P

def Ty.listItems {t : Ty} (xs : (Ty.list t).den) : List t.den := xs
def Ty.bagItems {t : Ty} (xs : (Ty.bag t).den) : List t.den := xs

def Ty.entries {k v : Ty} (x : (Ty.table k v).den) : List (k.den × v.den) := x.1

mutual
/-- Every kept function the value holds, or a function returns at arguments that reach only `P`, is a record of
`P`. -/
def Reach : (t : Ty) → t.den → Prop
  | .int, _ | .str, _ | .param _, _ | .date, _ | .id, _ => True
  | .list t, xs => ∀ x ∈ Ty.listItems xs, Reach t x
  | .bag t, xs => ∀ x ∈ Ty.bagItems xs, Reach t x
  | .table k v, x => ∀ e ∈ Ty.entries x, Reach k e.1 ∧ Reach v e.2
  | .tuple ts, x => Reaches ts x
  | .adt _ _ vs, x => ReachAlts vs x
  | .fn ps r, f => ∀ xs, Reaches ps xs → Reach r (f xs)
  | .dsl .closure [t], f => Fun.asSite (t := t) f ∈ P
  | .dsl .externalQuery [_, _], x => x.2.asSite ∈ P
  | .dsl .effect [_], x => EffectV.Reach P x
  | .dsl .effectClosure [.fn _ _], f => EffectFun.Reach P E f
  | .dsl .command [_, _, _, _, _], x => CommandV.Reach P x.1
  | .dsl .query [_, _, _, _], x => QueryV.Reach P x.1
  | .dsl .declared _, d => DeclaredV.Reach P d
  | .dsl .subscription [_], x => (x : SubscriptionV _).wrap.asSite ∈ P
  | .dsl .response [_], r => (r : ResponseV _).after.asSite ∈ P ∧ r.then_.asSite ∈ P
  | .dsl .create [_], x => (x : CreateV _).table.asSite ∈ P
  | .dsl .bounds [_], b => ∀ x ∈ (b : BoundsV _).creates, x.table.asSite ∈ P
  | .dsl .machine [_, _], m => MachineV.Reach P E m
  | .dsl .reaction [_, _], x => ReactionV.Reach P E x
  | .dsl .service _, v => ServiceV.Reach P E v
  | .dsl .spec _, s => ∀ v ∈ (s : SpecV).services, ServiceV.Reach P E v
  | .dsl _ _, _ => True
def Reaches : (ts : List Ty) → Ty.dens ts → Prop
  | [], _ => True
  | t :: ts, (x, xs) => Reach t x ∧ Reaches ts xs
def ReachAlts : (vs : List (List Ty)) → Ty.alts vs → Prop
  | [], e => nomatch e
  | fs :: _, .inl x => Reaches fs x
  | _ :: vs, .inr y => ReachAlts vs y
end

variable {E}


mutual
/-- Data holds no kept function. -/
theorem reach_data : (t : Ty) → t.isData = true → (x : t.den) → Reach P E t x
  | .int, _, _ | .str, _, _ | .param _, _, _ | .date, _, _ | .id, _, _ => trivial
  | .list t, h, xs => fun x _ => reach_data t (by simpa [Ty.isData] using h) x
  | .bag t, h, xs => fun x _ => reach_data t (by simpa [Ty.isData] using h) x
  | .table k v, h, x => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    exact fun e _ => ⟨reach_data k h.1 e.1, reach_data v h.2 e.2⟩
  | .tuple ts, h, x => reaches_data ts (by simpa [Ty.isData] using h) x
  | .adt _ _ vs, h, x => reachAlts_data vs (by simpa [Ty.isData] using h) x
  | .fn ps r, h, f => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    exact fun xs _ => reach_data r h.2 (f xs)
  | .dsl k a, h, x => by
    simp only [Ty.isData, beq_iff_eq] at h
    subst h
    simp [Reach]
theorem reaches_data : (ts : List Ty) → Ty.isDatas ts = true → (xs : Ty.dens ts) → Reaches P E ts xs
  | [], _, _ => trivial
  | t :: ts, h, (x, xs) => by
    simp only [Ty.isDatas, Bool.and_eq_true] at h
    exact ⟨reach_data t h.1 x, reaches_data ts h.2 xs⟩
theorem reachAlts_data : (vs : List (List Ty)) → Ty.isDatass vs = true → (x : Ty.alts vs) → ReachAlts P E vs x
  | [], _, e => nomatch e
  | fs :: _, h, .inl x => by
    simp only [Ty.isDatass, Bool.and_eq_true] at h
    exact reaches_data fs h.1 x
  | _ :: vs, h, .inr y => by
    simp only [Ty.isDatass, Bool.and_eq_true] at h
    exact reachAlts_data vs h.2 y
end


theorem Var.reach : {Γ : List Ty} → {t : Ty} → (v : Var Γ t) → (ρ : Ty.dens Γ) → Reaches P E Γ ρ → Reach P E t (v.get ρ)
  | _ :: _, _, .here, (_, _), h => h.1
  | _ :: _, _, .there v, (_, _), h => Var.reach v _ h.2

theorem Dens.reach_append : {a b : List Ty} → (xs : Ty.dens a) → (ys : Ty.dens b) → Reaches P E a xs → Reaches P E b ys →
    Reaches P E (a ++ b) (Dens.append xs ys)
  | [], _, (), _, _, h => h
  | _ :: _, _, (_, xs), ys, h, h' => ⟨h.1, Dens.reach_append xs ys h.2 h'⟩

theorem Dens.reach_get : {ts : List Ty} → (xs : Ty.dens ts) → (k : Fin ts.length) → Reaches P E ts xs →
    Reach P E (ts.get k) (Dens.get xs k)
  | _ :: _, (_, _), ⟨0, _⟩, h => h.1
  | _ :: _, (_, xs), ⟨k + 1, hk⟩, h => Dens.reach_get xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩ h.2

theorem Dens.reach_field : {ts : List Ty} → {t : Ty} → (xs : Ty.dens ts) → (k : Nat) → (hk : ts[k]? = some t) →
    Reaches P E ts xs → Reach P E t (Dens.field xs k hk)
  | [], _, _, _, hk, _ => nomatch hk
  | u :: _, t, (x, _), 0, hk, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk; exact h.1
  | _ :: _, _, (_, xs), k + 1, hk, h => Dens.reach_field xs k _ h.2

theorem Alts.reach_inj : {vs : List (List Ty)} → (v : Fin vs.length) → (x : Ty.dens (vs.get v)) →
    Reaches P E (vs.get v) x → ReachAlts P E vs (Alts.inj v x)
  | _ :: _, ⟨0, _⟩, _, h => h
  | _ :: _, ⟨k + 1, hk⟩, x, h => Alts.reach_inj (vs := _) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ x h

theorem Alts.reach_view : {vs : List (List Ty)} → (x : Ty.alts vs) → ReachAlts P E vs x →
    Reaches P E (vs.get (Alts.view x).1) (Alts.view x).2
  | [], e, _ => nomatch e
  | _ :: _, .inl _, h => h
  | _ :: _, .inr y, h => Alts.reach_view y h

theorem Alts.reach_proj : {vs : List (List Ty)} → (x : Ty.alts vs) → (v : Fin vs.length) → {y : Ty.dens (vs.get v)} →
    Alts.proj x v = some y → ReachAlts P E vs x → Reaches P E (vs.get v) y
  | _ :: _, .inl _, ⟨0, _⟩, _, hp, h => by simp only [Alts.proj, Option.some.injEq] at hp; subst hp; exact h
  | _ :: _, .inr y, ⟨k + 1, hk⟩, _, hp, h => Alts.reach_proj y ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hp h
  | _ :: _, .inl _, ⟨_ + 1, _⟩, _, hp, _ => by cases hp
  | _ :: _, .inr _, ⟨0, _⟩, _, hp, _ => by cases hp

mutual
theorem Pat.reach_match {t : Ty} {Δ : List Ty} : (p : Pat t Δ) → (x : t.den) → {δ : Ty.dens Δ} → p.match x = some δ →
    Reach P E t x → Reaches P E Δ δ
  | .wild, _, _, _, _ => trivial
  | .bind, _, _, hm, h => by cases hm; exact ⟨h, trivial⟩
  | .int _, _, _, _, _ | .str _, _, _, _, _ => trivial
  | .tuple ps, x, _, hm, h => Pats.reach_match ps x hm h
  | .ctor v ps, x, _, hm, h => by
    simp only [Pat.match, Option.bind_eq_some_iff] at hm
    obtain ⟨y, hy, hm⟩ := hm
    exact Pats.reach_match ps y hm (Alts.reach_proj P x v hy h)
  | .as p, x, _, hm, h => by
    simp only [Pat.match, Option.map_eq_some_iff] at hm
    obtain ⟨δ, hδ, rfl⟩ := hm
    exact Dens.reach_append P (b := [t]) δ (x, ()) (Pat.reach_match p x hδ h) ⟨h, trivial⟩
theorem Pats.reach_match {ts : List Ty} {Δ : List Ty} : (ps : Pats ts Δ) → (xs : Ty.dens ts) → {δ : Ty.dens Δ} →
    Pats.match ps xs = some δ → Reaches P E ts xs → Reaches P E Δ δ
  | .nil, (), _, _, _ => trivial
  | .cons p ps, (x, xs), _, hm, h => by
    simp only [Pats.match, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    exact Dens.reach_append P a b (Pat.reach_match p x ha h.1) (Pats.reach_match ps xs hb h.2)
end

theorem reach_fn_data {ps : List Ty} {r : Ty} (hr : r.isData = true) (f : (Ty.fn ps r).den) : Reach P E (.fn ps r) f :=
  fun xs _ => reach_data P r hr (f xs)

theorem lookupBy_mem {κ ν : Type} (f : κ → κ → Bool) (k : κ) : (xs : List (κ × ν)) → {v : ν} → lookupBy f k xs = some v →
    ∃ e ∈ xs, e.2 = v
  | [], _, h => by cases h
  | (k', w) :: rest, v, h => by
    simp only [lookupBy] at h
    split at h
    · cases h; exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨e, he, rfl⟩ := lookupBy_mem f k rest h; exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩

theorem pick_mem {α : Type} (wins : Int → Int → Bool) (key : α → Int) (xs : List α) {w : α}
    (h : Builtin.pick wins key xs = .ok w) : w ∈ xs := by
  unfold Builtin.pick at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · rename_i hf; cases h
      have hm : w ∈ [w] := List.mem_singleton_self w
      rw [← hf] at hm
      exact (List.mem_filter.1 hm).1
    · cases h

theorem reach_insert {k v : Ty} (key : k.den) (val : v.den) (t : (Ty.table k v).den) (hk : Reach P E k key)
    (hv : Reach P E v val) (ht : ∀ e ∈ Ty.entries t, Reach P E k e.1 ∧ Reach P E v e.2) :
    ∀ e ∈ Ty.entries (Builtin.tableInsert key val t), Reach P E k e.1 ∧ Reach P E v e.2 := by
  intro e he
  simp only [Ty.entries, Builtin.tableInsert, Builtin.tableRemove, List.mem_append, List.mem_filter,
    List.mem_singleton] at he
  rcases he with ⟨he, -⟩ | rfl
  · exact ht e he
  · exact ⟨hk, hv⟩

theorem foldl_inv {α β : Type} (Q : β → Prop) (R : α → Prop) (f : β → α → β) (hf : ∀ b a, Q b → R a → Q (f b a)) :
    (xs : List α) → (b : β) → (∀ a ∈ xs, R a) → Q b → Q (xs.foldl f b)
  | [], _, _, hb => hb
  | a :: xs, b, hx, hb => foldl_inv Q R f hf xs (f b a) (fun a' h => hx a' (List.mem_cons_of_mem _ h))
      (hf b a hb (hx a List.mem_cons_self))

/-- Every built-in reaches only `P`: it builds no kept function, so what it returns holds only what its arguments do. -/
theorem Prim.reach (p : Prim) (args : List Ty) (h : p.ok args = true) : Reach P E (p.ty.inst args) (p.den args h) := by
  cases p
  all_goals simp only [Prim.ty, Prim.sig, List.map, Ty.inst, Ty.insts]
  all_goals first
    | exact reach_fn_data P rfl _
    | (simp only [Reach, DeclaredV.Reach]; intro _ _; trivial)
    | skip
  case bagFromList => exact fun ⟨xs, ()⟩ hx => hx.1
  case bagInsert =>
    rintro ⟨xs, x, ⟨⟩⟩ ⟨hb, hx, -⟩ y hy
    cases hy with
    | head => exact hx
    | tail _ hy => exact hb y hy
  case bagFilter =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨hb, -, -⟩ y hy
    exact hb y (List.mem_filter.1 hy).1
  case bagMap =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨hb, hf, -⟩ y hy
    change y ∈ List.map (fun x => f (x, ())) xs at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hf (x, ()) ⟨hb x hx, trivial⟩
  case bagMinBy | bagMaxBy =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨hb, -, -⟩
    change ReachAlts P E _ (Ty.ofPick (Builtin.pick _ (fun x => f (x, ())) xs))
    cases hp : Builtin.pick _ (fun x => f (x, ())) xs with
    | ok w => exact ⟨hb w (pick_mem _ _ _ hp), trivial⟩
    | error b => cases b <;> exact ⟨reach_data P _ rfl _, trivial⟩
  case tableNew => intro _ _ e he; cases he
  case tableFromList =>
    rintro ⟨pairs, ⟨⟩⟩ ⟨hp, -⟩
    dsimp only [Prim.den]
    refine foldl_inv (fun t => ∀ e ∈ Ty.entries t, Reach P E _ e.1 ∧ Reach P E _ e.2) (Reaches P E [_, _]) _ ?_ pairs _ hp
      (fun e he => by cases he)
    rintro t ⟨k, v, ⟨⟩⟩ ht hkv
    exact reach_insert P k v t hkv.1 hkv.2.1 ht
  case tableInsert =>
    rintro ⟨t, k, v, ⟨⟩⟩ ⟨ht, hk, hv, -⟩
    exact reach_insert P k v t hk hv ht
  case tableRemove =>
    rintro ⟨t, k, ⟨⟩⟩ ⟨ht, -, -⟩ e he
    exact ht e (List.mem_filter.1 he).1
  case tableGet =>
    rintro ⟨t, k, ⟨⟩⟩ ⟨ht, -, -⟩
    change ReachAlts P E _ (match lookupBy _ k t.1 with | .some v => Ty.some v | .none => Ty.none)
    cases hl : lookupBy _ k t.1 with
    | some v =>
      obtain ⟨e, he, rfl⟩ := lookupBy_mem _ _ _ hl
      exact ⟨(ht e he).2, trivial⟩
    | none => exact trivial
  case tableKeys =>
    rintro ⟨t, ⟨⟩⟩ ⟨ht, -⟩ y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    exact (ht e he).1
  case tableValues =>
    rintro ⟨t, ⟨⟩⟩ ⟨ht, -⟩ y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    exact (ht e he).2
  case tableFilter =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨ht, -, -⟩ e he
    exact ht e (List.mem_filter.1 he).1
  case tableMap =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨ht, hf, -⟩ e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact ⟨(ht e' he').1, hf (e'.1, e'.2, ()) ⟨(ht e' he').1, (ht e' he').2, trivial⟩⟩
  case require =>
    rintro ⟨b, rej, next, ⟨⟩⟩ ⟨-, hr, hn, -⟩
    dsimp only [Prim.den]
    have key : ∀ c : Bool, Reach P E (Ty.inst args ((Ty.param 0).result (Ty.param 1)))
        (if c = true then next () else Ty.error rej) := fun c => by
      cases c
      · exact ⟨hr, trivial⟩
      · exact hn () trivial
    exact key _
  case tableLookup =>
    rintro ⟨t, k, rej, next, ⟨⟩⟩ ⟨ht, -, hr, hn, -⟩
    change ReachAlts P E _ (match lookupBy _ k t.1 with | .some v => next (v, ()) | .none => Ty.error rej)
    cases hl : lookupBy _ k t.1 with
    | some v =>
      obtain ⟨e, he, rfl⟩ := lookupBy_mem _ _ _ hl
      exact hn (e.2, ()) ⟨(ht e he).2, trivial⟩
    | none => exact ⟨hr, trivial⟩
  case machine =>
    rintro ⟨name, inst, init, on, after, eff, inv, ⟨⟩⟩ ⟨-, hi, -, ho, ha, he, hv, -⟩
    exact ⟨he, hi, ho, ha, hv⟩
  case reaction =>
    rintro ⟨name, react, ⟨⟩⟩ ⟨-, hr, -⟩
    exact hr
  case response =>
    rintro ⟨name, after, then_, within, ⟨⟩⟩ ⟨-, ha, ht, -⟩
    exact ⟨ha, ht⟩
  case create =>
    rintro ⟨table, atMost, ⟨⟩⟩ ⟨ht, -⟩
    exact ht
  case bounds =>
    rintro ⟨creates, items, cascade, steps, ⟨⟩⟩ ⟨hc, -⟩
    exact hc
  case command =>
    rintro ⟨name, callers, accepts, decide, ensures, ⟨⟩⟩ ⟨-, -, ha, hd, he, -⟩
    exact ⟨ha, hd, he⟩
  case query =>
    rintro ⟨name, callers, accepts, resolve, ⟨⟩⟩ ⟨-, -, ha, hr, -⟩
    exact ⟨ha, hr⟩
  case declareCommand | declareQuery =>
    rintro ⟨x, ⟨⟩⟩ ⟨hx, -⟩
    exact hx
  case subscribe =>
    rintro ⟨name, wrap, ⟨⟩⟩ ⟨-, hw, -⟩
    exact hw
  case service =>
    rintro ⟨name, init, apply, subs, decl, ms, xs, inv, resp, bnds, scs, ⟨⟩⟩ ⟨-, -, ha, hs, hd, hm, hx, hi, hr, hb, -⟩
    refine ⟨hm, hx, ha, hi, fun x hx' => ?_, fun x hx' => ?_, hs, hr, hb⟩
    · obtain ⟨d, hdm, hdx⟩ := List.mem_filterMap.1 hx'
      have hdr := hd d hdm
      cases d with
      | command r e c y =>
        dsimp only at hdx
        split at hdx
        · rename_i h1 h2 h3 _ _ _
          cases hdx; subst h1 h2 h3; exact hdr
        · cases hdx
      | _ => cases hdx
    · obtain ⟨d, hdm, hdx⟩ := List.mem_filterMap.1 hx'
      have hdr := hd d hdm
      cases d with
      | query r c y =>
        dsimp only at hdx
        split at hdx
        · rename_i h1 h2 _ _
          cases hdx; subst h1 h2; exact hdr
        · cases hdx
      | _ => cases hdx
  case spec =>
    rintro ⟨services, externals, ⟨⟩⟩ ⟨hs, -, -⟩ v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    have h : ServiceV.Reach P E w := hs w hw
    refine ⟨h.machines, h.reactions, h.apply, h.invariants, h.commands, h.queries, fun x hx => ?_, h.responses,
      h.creates⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact h.subscribes y hy
  case externalQuery =>
    rintro ⟨name, ens, ⟨⟩⟩ ⟨-, he, -⟩
    exact he
  case requestCommand =>
    rintro ⟨name, input, oa, ⟨⟩⟩ ⟨-, -, ho, -⟩
    exact ⟨ho, (fun f hf => by cases hf), Ty.isData_inst (Prim.dataOf h rfl) (.param 1) rfl, rfl⟩
  case requestQuery =>
    rintro ⟨⟨name, ens⟩, input, oa, ⟨⟩⟩ ⟨he, -, ho, -⟩
    exact ⟨ho, (fun f hf => by cases hf; exact he), Ty.isData_inst (Prim.dataOf h rfl) (.param 1) rfl, rfl⟩
  case sendCommand =>
    rintro ⟨c, caller, input, oa, ⟨⟩⟩ ⟨-, -, -, ho, -⟩
    exact ho
  case sendQuery =>
    rintro ⟨c, caller, input, oa, ⟨⟩⟩ ⟨-, -, -, ho, -⟩
    exact ho


omit P in
theorem sub_l {α : Type} {a b : List α} {Q : α → Prop} (h : ∀ x ∈ a ++ b, Q x) : ∀ x ∈ a, Q x :=
  fun x hx => h x (List.mem_append_left _ hx)
omit P in
theorem sub_r {α : Type} {a b : List α} {Q : α → Prop} (h : ∀ x ∈ a ++ b, Q x) : ∀ x ∈ b, Q x :=
  fun x hx => h x (List.mem_append_right _ hx)

omit P in
theorem BinOp.data {a b c : Ty} : BinOp a b c → c.isData = true
  | .add | .sub | .mul | .div | .mod | .lt | .le | .gt | .ge | .and | .or | .concat | .eq _ | .ne _ => rfl

section
variable {G : List Ty} (D : Defs G) (g : Ty.dens G)
  (hg : ∀ {t : Ty} (v : Var G t), (∀ s ∈ D.usesAt sitesC v.idx, s ∈ P) → Reach P E t (v.get g))
  (hDE : ∀ s ∈ D.effectSites, s ∈ E)
include hg hDE

set_option linter.unusedSectionVars false

/-- The kept functions every global of `gs` holds are sites of `P`. -/
abbrev GlobalsIn (gs : List Nat) : Prop := ∀ i ∈ gs, ∀ s ∈ D.usesAt sitesC i, s ∈ P

mutual
/-- Evaluation reaches only `P` and `E` when the expression's sites and effect sites, the globals it reads and the
variables do. -/
theorem Expr.reach {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → (∀ s ∈ e.sites D, s ∈ P) → GlobalsIn P D e.globals →
    (∀ s ∈ e.effectSites D, s ∈ E) → (ρ : Ty.dens Γ) → Reaches P E Γ ρ → Reach P E t (e.eval D g ρ)
  | .int _, _, _, _, _, _ | .str _, _, _, _, _, _ => trivial
  | .var v, _, _, _, ρ, hρ => Var.reach P v ρ hρ
  | .global v, _, hu, _, _, _ => hg v (hu _ (by simp [Expr.globals]))
  | .ctor v es, hs, hu, he, ρ, hρ => Alts.reach_inj P v _ (Exprs.reach es hs hu he ρ hρ)
  | .field _ k hk e, hs, hu, he, ρ, hρ => by
    have he := Alts.reach_view P _ (Expr.reach e hs hu he ρ hρ)
    simp only [Expr.eval]
    exact Dens.reach_field P _ k _ he
  | .index e k, hs, hu, he, ρ, hρ => Dens.reach_get P _ k (Expr.reach e hs hu he ρ hρ)
  | .update e p, hs, hu, he, ρ, hρ => by
    have hx := Expr.reach e (sub_l hs) (sub_l hu) (sub_l he) ρ hρ
    simp only [Expr.eval]
    refine Alts.reach_inj P ⟨0, by simp⟩ _ (Patch.reach p (sub_r hs) (sub_r hu) (sub_r he) ρ hρ _ ?_)
    revert hx
    generalize Expr.eval D g e ρ = x
    match x with
    | .inl y => exact id
  | .call f args, hs, hu, he, ρ, hρ =>
    (Expr.reach f (sub_l hs) (sub_l hu) (sub_l he) ρ hρ) _ (Exprs.reach args (sub_r hs) (sub_r hu) (sub_r he) ρ hρ)
  | .lam body, hs, hu, he, ρ, hρ => fun xs hxs => Expr.reach body hs hu he _ (Dens.reach_append P xs ρ hxs hρ)
  | .let_ e body, hs, hu, he, ρ, hρ =>
    Expr.reach body (sub_r hs) (sub_r hu) (sub_r he) _ ⟨Expr.reach e (sub_l hs) (sub_l hu) (sub_l he) ρ hρ, hρ⟩
  | .case e cs hc, hs, hu, he, ρ, hρ =>
    Clauses.reach cs (sub_r hs) (sub_r hu) (sub_r he) ρ hρ _ (Expr.reach e (sub_l hs) (sub_l hu) (sub_l he) ρ hρ) _
  | .list items, hs, hu, he, ρ, hρ => Items.reach items hs hu he ρ hρ
  | .tuple es, hs, hu, he, ρ, hρ => Exprs.reach es hs hu he ρ hρ
  | .bin op _ _, _, _, _, _, _ => reach_data P _ op.data _
  | .not _, _, _, _, _, _ => reach_data P _ rfl _
  | .neg _, _, _, _, _, _ => trivial
  | .prim p args h, _, _, _, _, _ => Prim.reach P p args h
  | .close site env hΓ ht body, hs, _, _, _, _ => hs _ List.mem_cons_self
  | .closeEffect _ _ _ _ body, hs, hu, he, _, _ =>
    ⟨he _ List.mem_cons_self, fun s h => by
      simp only [EffectFun.usedSites, Expr.uses, Expr.usesWith, List.mem_append, List.mem_flatMap] at h
      rcases h with h | ⟨i, hi, h⟩
      · exact sub_r hs s h
      · exact sub_r hu i hi s h,
      fun _ h => he _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)), hDE⟩
theorem Exprs.reach {Γ ts : List Ty} : (es : Exprs G Γ ts) → (∀ s ∈ Exprs.sites D es, s ∈ P) →
    GlobalsIn P D (Exprs.globals es) → (∀ s ∈ Exprs.effectSites D es, s ∈ E) → (ρ : Ty.dens Γ) → Reaches P E Γ ρ →
    Reaches P E ts (Exprs.eval D g es ρ)
  | .nil, _, _, _, _, _ => trivial
  | .cons e es, hs, hu, he, ρ, hρ =>
    ⟨Expr.reach e (sub_l hs) (sub_l hu) (sub_l he) ρ hρ, Exprs.reach es (sub_r hs) (sub_r hu) (sub_r he) ρ hρ⟩
theorem Items.reach {Γ : List Ty} {t : Ty} : (items : Items G Γ t) → (∀ s ∈ Items.sites D items, s ∈ P) →
    GlobalsIn P D (Items.globals items) → (∀ s ∈ Items.effectSites D items, s ∈ E) → (ρ : Ty.dens Γ) →
    Reaches P E Γ ρ → ∀ x ∈ Items.eval D g items ρ, Reach P E t x
  | .nil, _, _, _, _, _, _, hx => by cases hx
  | .cons e es, hs, hu, he, ρ, hρ, x, hx => by
    cases hx with
    | head => exact Expr.reach e (sub_l hs) (sub_l hu) (sub_l he) ρ hρ
    | tail _ hx => exact Items.reach es (sub_r hs) (sub_r hu) (sub_r he) ρ hρ x hx
theorem Patch.reach {Γ ts : List Ty} : (p : Patch G Γ ts) → (∀ s ∈ Patch.sites D p, s ∈ P) →
    GlobalsIn P D (Patch.globals p) → (∀ s ∈ Patch.effectSites D p, s ∈ E) → (ρ : Ty.dens Γ) → Reaches P E Γ ρ →
    (xs : Ty.dens ts) → Reaches P E ts xs → Reaches P E ts (Patch.eval D g p ρ xs)
  | .nil, _, _, _, _, _, (), _ => trivial
  | .keep rest, hs, hu, he, ρ, hρ, (_, xs), hx => ⟨hx.1, Patch.reach rest hs hu he ρ hρ xs hx.2⟩
  | .set e rest, hs, hu, he, ρ, hρ, (_, xs), hx =>
    ⟨Expr.reach e (sub_l hs) (sub_l hu) (sub_l he) ρ hρ, Patch.reach rest (sub_r hs) (sub_r hu) (sub_r he) ρ hρ xs hx.2⟩
theorem Clauses.reach {Γ : List Ty} {t r : Ty} {sh : List Shape} : (cs : Clauses G Γ t r sh) →
    (∀ s ∈ Clauses.sites D cs, s ∈ P) → GlobalsIn P D (Clauses.globals cs) →
    (∀ s ∈ Clauses.effectSites D cs, s ∈ E) → (ρ : Ty.dens Γ) →
    Reaches P E Γ ρ → (x : t.den) → Reach P E t x →
    (h : ∃ s ∈ sh, Shape.Matches t s x) → Reach P E r (Clauses.eval D g cs ρ x h)
  | .nil, _, _, _, _, _, _, _, h => False.elim (by simp at h)
  | .cons p body rest, hs, hu, he, ρ, hρ, x, hx, h => by
    simp only [Clauses.eval]
    split
    · rename_i δ hm
      exact Expr.reach body (sub_l hs) (sub_l hu) (sub_l he) _ (Dens.reach_append P δ ρ (Pat.reach_match P p x hm hx) hρ)
    · exact Clauses.reach rest (sub_r hs) (sub_r hu) (sub_r he) ρ hρ x hx _
  | .guarded p guard body rest, hs, hu, he, ρ, hρ, x, hx, h => by
    simp only [Clauses.eval]
    split
    · rename_i δ hm
      split
      · exact Expr.reach body (sub_r (sub_l hs)) (sub_r (sub_l hu)) (sub_r (sub_l he)) _
          (Dens.reach_append P δ ρ (Pat.reach_match P p x hm hx) hρ)
      · exact Clauses.reach rest (sub_r hs) (sub_r hu) (sub_r he) ρ hρ x hx h
    · exact Clauses.reach rest (sub_r hs) (sub_r hu) (sub_r he) ρ hρ x hx h
end

end

/-- Every global reaches only `P` and `E` when the kept functions it and the globals it reads write are sites of `P`
and the definitions' effect sites are in `E`. -/
theorem Defs.reach : {G : List Ty} → (D : Defs G) → (∀ s ∈ D.effectSites, s ∈ E) → {t : Ty} → (v : Var G t) →
    (∀ s ∈ D.usesAt sitesC v.idx, s ∈ P) → Reach P E t (v.get D.eval)
  | _ :: _, .snoc defs _ body, hE, _, .here, hu => by
    simp only [Defs.usesAt, Defs.uses, Var.idx, List.getD_cons_zero, Expr.usesWith, sitesC] at hu
    exact Expr.reach P defs defs.eval (fun v h => Defs.reach defs (sub_l hE) v h) (sub_l hE) body (sub_l hu)
      (fun i hi s h => sub_r hu s (List.mem_flatMap.2 ⟨i, hi, h⟩)) (sub_r hE) () trivial
  | _ :: _, .snoc defs _ _, hE, _, .there v, hu => by
    simp only [Defs.usesAt, Defs.uses, Var.idx, List.getD_cons_succ] at hu
    exact Defs.reach defs (sub_l hE) v hu

/-- The structure a program evaluates to reaches only the program's sites and effect sites. -/
theorem Program.reach {t : Ty} (p : Program t) : Reach p.defs.sites p.defs.effectSites t p.eval :=
  Defs.reach _ p.defs (fun _ h => h) p.root fun s h => Defs.collect_sites p.defs ▸ Defs.uses_sub sitesC p.defs _ s h

/-- What a kept function that returns effects returns reaches only `P` and `E`. -/
theorem EffectFun.reach_apply {ps : List Ty} {r : Ty} (f : EffectFun ps r) (hf : f.Reach P E)
    (xs : (Ty.tuple ps).den0) : Tazuna.Ir.Reach P E r (f.apply xs) := by
  have hu := hf.used
  simp only [EffectFun.usedSites, Expr.uses, Expr.usesWith, sitesC] at hu
  exact Expr.reach P f.defs f.defs.eval (fun v h => Defs.reach P f.defs hf.defsEffectSites v h) hf.defsEffectSites
    f.body (sub_l hu) (fun i hi s h => sub_r hu s (List.mem_flatMap.2 ⟨i, hi, h⟩)) hf.effectSites _
    (reach_data P (.tuple f.Γ) f.hΓ _) _ (reach_data P (.tuple ps) f.hps _)

/-- A kept function that returns effects reaches the kept functions its source and the globals it reads write. -/
theorem EffectFun.reach_own {ps : List Ty} {r : Ty} {f : EffectFun ps r} (hf : f.Reach P E) :
    f.Reach f.usedSites E :=
  ⟨hf.site, fun _ h => h, hf.effectSites, hf.defsEffectSites⟩

/-- The effect a machine's instance starts names only records of `P`. -/
theorem MachineV.reach_effectAt {r e : Ty} (m : MachineV r e) (hm : m.effect.Reach P E) (key : m.key.den0)
    (st : m.state.den0) (records : r.den0) (now : Int) : ∀ eff ∈ m.effectAt key st records now, eff.Reach P := by
  intro eff heff
  have h := EffectFun.reach_apply P m.effect hm (.inl (key, st, records, now, ()), ())
  simp only [MachineV.effectAt] at heff
  revert h heff
  generalize m.effect.apply (.inl (key, st, records, now, ()), ()) = x
  match x with
  | .inl (y, ()) => intro heff h; cases heff; exact h.1
  | .inr _ => intro heff _; cases heff

/-- So do the effects a reaction starts. -/
theorem ReactionV.reach_effectsAt {r e : Ty} (x : ReactionV r e) (hx : x.Reach P E) (ev : e.den0) (records : r.den0)
    (now : Int) : ∀ eff ∈ x.effectsAt ev records now, eff.Reach P :=
  EffectFun.reach_apply P x.react hx ((.inl (records, now, ()), ev, ()))

end

/-- A closure's id fixes its source: a kept function that is a record of the unique sites `P` is the closure record
of `P`'s site with its id, at its captured values. -/
theorem Fun.eq_siteFn {P : List AnySite} (hP : SitesUnique P) {Γ : List Ty} {t : Ty} (f : Fun t) (s : Site Γ t)
    (hf : f.asSite ∈ P) (hs : ⟨Γ, t, s⟩ ∈ P) (h : f.site = s.site) : ∃ e : f.Γ = Γ, f = s.fn (e ▸ f.env) := by
  have he := site_eq hP hf hs h
  obtain ⟨site, G, defs, Γf, env, hΓ, ht, body⟩ := f
  simp only [Fun.asSite, Sigma.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  simp only [heq_eq_eq, Sigma.mk.injEq, true_and] at he
  subst he
  exact ⟨rfl, rfl⟩

end Tazuna.Ir
