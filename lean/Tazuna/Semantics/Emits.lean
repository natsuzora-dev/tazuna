import Tazuna.Semantics.PendingInv
import Tazuna.Semantics.StepRename
import Tazuna.Semantics.GenTarget

/-! Which constructors of the event type a step can apply, read off the code it runs (the cone of influence of the
step's events). A value of the event type is built only by a constructor written in the code (`Expr.ctor`, or a record
update) or comes from a value the code is given; so where no value a step starts from can hold an event (no type of the
state or of an input names the event type), every event the step applies is built by a constructor written in a
function it runs (`step_emits`). The functions are the input's own (a command's `decide`, a subscription's `wrap`, the
`on_answer` of a pending request) and the cascade's: every machine's `effect`, every reaction, and every command the
service may run as `Own`. A request's `on_answer` written inside them runs only when its answer comes, so its
constructors are not the cascade's. `Ok` is the logical relation behind it: every event a value holds, or a function
returns at arguments that hold only allowed events, is built with an allowed constructor; evaluation keeps it
(`Expr.ok`) as it keeps `Reach`. -/

namespace Tazuna.Ir

mutual
/-- Whether a value of the type can hold a value of the type declaration `i`. -/
def Ty.mentions (i : Nat) : Ty → Bool
  | .adt j a vs => j == i || Ty.mentionsL i a || Ty.mentionsLL i vs
  | .list t | .bag t => Ty.mentions i t
  | .tuple ts => Ty.mentionsL i ts
  | .fn ps r => Ty.mentionsL i ps || Ty.mentions i r
  | .table k w => Ty.mentions i k || Ty.mentions i w
  | .dsl _ a => Ty.mentionsL i a
  | .int | .str | .param _ | .date | .id => false
def Ty.mentionsL (i : Nat) : List Ty → Bool
  | [] => false
  | t :: ts => Ty.mentions i t || Ty.mentionsL i ts
def Ty.mentionsLL (i : Nat) : List (List Ty) → Bool
  | [] => false
  | ts :: vs => Ty.mentionsL i ts || Ty.mentionsLL i vs
end

/-- The variant a value of a custom type is, counted from 0. -/
def Alts.index {vs : List (List Ty)} (x : Ty.alts vs) : Nat := (Alts.view x).1.val

/-- What a kept function that returns effects means, as `Fun.eval` for a kept function. -/
def EffectFun.eval {ps : List Ty} {r : Ty} (f : EffectFun ps r) : (Ty.fn ps r).den :=
  f.body.eval f.defs f.defs.eval (Ty.up _ f.hΓ f.env)

section
variable (i : Nat) (okV : Nat → Prop)

mutual
/-- Every value of the type declaration `i` that the value holds, or that a function returns at arguments for which
this holds, is built with a constructor `okV` allows. A kept function is read by its meaning; an effect by the events
its `on_answer` returns at any answer of a type that cannot hold such a value. A request's `on_answer` runs only in a
later step, so a request is not read. -/
def Ok : (t : Ty) → t.den → Prop
  | .int, _ | .str, _ | .param _, _ | .date, _ | .id, _ => True
  | .list t, xs => ∀ x ∈ Ty.listItems xs, Ok t x
  | .bag t, xs => ∀ x ∈ Ty.bagItems xs, Ok t x
  | .table k w, x => ∀ e ∈ Ty.entries x, Ok k e.1 ∧ Ok w e.2
  | .tuple ts, x => Oks ts x
  | .adt j _ vs, x => (j = i → okV (Alts.index x)) ∧ OkAlts vs x
  | .fn ps r, f => ∀ xs, Oks ps xs → Ok r (f xs)
  | .dsl .closure [t], f => Ok t (Fun.eval (t := t) f)
  | .dsl .effect [e], x => match (x : EffectV e) with
    | .request _ => True
    | .command _ _ _ j _ f => Ty.mentions i j = false →
        ∀ y, ∀ z ∈ Ty.listItems ((Fun.eval f : (Ty.fn [Ty.result Ty.nil j] (.list e)).den) y), Ok e z
    | .query _ _ _ o _ f => Ty.mentions i o = false →
        ∀ y, ∀ z ∈ Ty.listItems ((Fun.eval f : (Ty.fn [o] (.list e)).den) y), Ok e z
  | .dsl .effectClosure [.fn ps r], f => ∀ xs, Oks ps xs → Ok r (EffectFun.eval (ps := ps) (r := r) f xs)
  | .dsl _ _, _ => True
def Oks : (ts : List Ty) → Ty.dens ts → Prop
  | [], _ => True
  | t :: ts, (x, xs) => Ok t x ∧ Oks ts xs
def OkAlts : (vs : List (List Ty)) → Ty.alts vs → Prop
  | [], e => nomatch e
  | fs :: _, .inl x => Oks fs x
  | _ :: vs, .inr y => OkAlts vs y
end

variable {i okV}

mutual
/-- A type that cannot hold a value of the declaration: every value of it is `Ok`. -/
theorem ok_free : (t : Ty) → t.mentions i = false → (x : t.den) → Ok i okV t x
  | .int, _, _ | .str, _, _ | .param _, _, _ | .date, _, _ | .id, _, _ => trivial
  | .list t, h, _ => fun x _ => ok_free t (by simpa [Ty.mentions] using h) x
  | .bag t, h, _ => fun x _ => ok_free t (by simpa [Ty.mentions] using h) x
  | .table k w, h, _ => by
    simp only [Ty.mentions, Bool.or_eq_false_iff] at h
    exact fun e _ => ⟨ok_free k h.1 e.1, ok_free w h.2 e.2⟩
  | .tuple ts, h, x => oks_free ts (by simpa [Ty.mentions] using h) x
  | .adt j _ vs, h, x => by
    simp only [Ty.mentions, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    exact ⟨fun e => absurd e h.1.1, okAlts_free vs h.2 x⟩
  | .fn ps r, h, f => by
    simp only [Ty.mentions, Bool.or_eq_false_iff] at h
    exact fun xs _ => ok_free r h.2 (f xs)
  | .dsl k a, h, x => by
    simp only [Ty.mentions] at h
    match k, a, h, x with
    | .closure, [t], h, f => exact ok_free t (by simpa [Ty.mentionsL] using h) _
    | .effect, [e], h, x =>
      have he : e.mentions i = false := by simpa [Ty.mentionsL] using h
      match x with
      | .request _ => trivial
      | .command .. => exact fun _ _ z _ => ok_free e he z
      | .query .. => exact fun _ _ z _ => ok_free e he z
    | .effectClosure, [.fn ps r], h, f =>
      have hr : r.mentions i = false := by
        simp only [Ty.mentionsL, Ty.mentions, Bool.or_eq_false_iff] at h; exact h.1.2
      exact fun xs _ => ok_free r hr _
    | .spec, _, _, _ | .service, _, _, _ | .command, _, _, _ | .query, _, _, _ | .machine, _, _, _
    | .reaction, _, _, _ | .external, _, _, _ | .externalCommand, _, _, _ | .externalQuery, _, _, _
    | .source, _, _, _ | .declared, _, _, _ | .subscription, _, _, _ | .bounds, _, _, _ | .create, _, _, _
    | .response, _, _, _ | .scenario, _, _, _ | .step, _, _, _ | .sender, _, _, _ | .fresh, _, _, _ => trivial
    | .closure, [], _, _ | .closure, _ :: _ :: _, _, _ | .effect, [], _, _ | .effect, _ :: _ :: _, _, _
    | .effectClosure, [], _, _ => trivial
    | .effectClosure, _ :: _ :: _, _, _ => simp [Ok]
    | .effectClosure, [.int], _, _ | .effectClosure, [.str], _, _ | .effectClosure, [.list _], _, _
    | .effectClosure, [.tuple _], _, _ | .effectClosure, [.adt ..], _, _ | .effectClosure, [.param _], _, _
    | .effectClosure, [.bag _], _, _ | .effectClosure, [.table ..], _, _ | .effectClosure, [.date], _, _
    | .effectClosure, [.id], _, _ | .effectClosure, [.dsl ..], _, _ => trivial
theorem oks_free : (ts : List Ty) → Ty.mentionsL i ts = false → (xs : Ty.dens ts) → Oks i okV ts xs
  | [], _, _ => trivial
  | t :: ts, h, (x, xs) => by
    simp only [Ty.mentionsL, Bool.or_eq_false_iff] at h
    exact ⟨ok_free t h.1 x, oks_free ts h.2 xs⟩
theorem okAlts_free : (vs : List (List Ty)) → Ty.mentionsLL i vs = false → (x : Ty.alts vs) → OkAlts i okV vs x
  | [], _, e => nomatch e
  | fs :: _, h, .inl x => by
    simp only [Ty.mentionsLL, Bool.or_eq_false_iff] at h
    exact oks_free fs h.1 x
  | _ :: vs, h, .inr y => by
    simp only [Ty.mentionsLL, Bool.or_eq_false_iff] at h
    exact okAlts_free vs h.2 y
end

theorem Var.ok : {Γ : List Ty} → {t : Ty} → (v : Var Γ t) → (ρ : Ty.dens Γ) → Oks i okV Γ ρ → Ok i okV t (v.get ρ)
  | _ :: _, _, .here, (_, _), h => h.1
  | _ :: _, _, .there v, (_, _), h => Var.ok v _ h.2

theorem Dens.ok_append : {a b : List Ty} → (xs : Ty.dens a) → (ys : Ty.dens b) → Oks i okV a xs → Oks i okV b ys →
    Oks i okV (a ++ b) (Dens.append xs ys)
  | [], _, (), _, _, h => h
  | _ :: _, _, (_, xs), ys, h, h' => ⟨h.1, Dens.ok_append xs ys h.2 h'⟩

theorem Dens.ok_get : {ts : List Ty} → (xs : Ty.dens ts) → (k : Fin ts.length) → Oks i okV ts xs →
    Ok i okV (ts.get k) (Dens.get xs k)
  | _ :: _, (_, _), ⟨0, _⟩, h => h.1
  | _ :: _, (_, xs), ⟨k + 1, hk⟩, h => Dens.ok_get xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩ h.2

theorem Dens.ok_field : {ts : List Ty} → {t : Ty} → (xs : Ty.dens ts) → (k : Nat) → (hk : ts[k]? = some t) →
    Oks i okV ts xs → Ok i okV t (Dens.field xs k hk)
  | [], _, _, _, hk, _ => nomatch hk
  | u :: _, t, (x, _), 0, hk, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk; exact h.1
  | _ :: _, _, (_, xs), k + 1, hk, h => Dens.ok_field xs k _ h.2

theorem Alts.okAlts_inj : {vs : List (List Ty)} → (v : Fin vs.length) → (x : Ty.dens (vs.get v)) →
    Oks i okV (vs.get v) x → OkAlts i okV vs (Alts.inj v x)
  | _ :: _, ⟨0, _⟩, _, h => h
  | _ :: _, ⟨k + 1, hk⟩, x, h => Alts.okAlts_inj (vs := _) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ x h

theorem Alts.index_inj {vs : List (List Ty)} (v : Fin vs.length) (x : Ty.dens (vs.get v)) :
    Alts.index (Alts.inj v x) = v.val := by
  simp [Alts.index, Alts.view_inj]

theorem Alts.ok_view : {vs : List (List Ty)} → (x : Ty.alts vs) → OkAlts i okV vs x →
    Oks i okV (vs.get (Alts.view x).1) (Alts.view x).2
  | [], e, _ => nomatch e
  | _ :: _, .inl _, h => h
  | _ :: _, .inr y, h => Alts.ok_view y h

theorem Alts.ok_proj : {vs : List (List Ty)} → (x : Ty.alts vs) → (v : Fin vs.length) → {y : Ty.dens (vs.get v)} →
    Alts.proj x v = some y → OkAlts i okV vs x → Oks i okV (vs.get v) y
  | _ :: _, .inl _, ⟨0, _⟩, _, hp, h => by simp only [Alts.proj, Option.some.injEq] at hp; subst hp; exact h
  | _ :: _, .inr y, ⟨k + 1, hk⟩, _, hp, h => Alts.ok_proj y ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hp h
  | _ :: _, .inl _, ⟨_ + 1, _⟩, _, hp, _ => by cases hp
  | _ :: _, .inr _, ⟨0, _⟩, _, hp, _ => by cases hp

mutual
theorem Pat.ok_match {t : Ty} {Δ : List Ty} : (p : Pat t Δ) → (x : t.den) → {δ : Ty.dens Δ} → p.match x = some δ →
    Ok i okV t x → Oks i okV Δ δ
  | .wild, _, _, _, _ => trivial
  | .bind, _, _, hm, h => by cases hm; exact ⟨h, trivial⟩
  | .int _, _, _, _, _ | .str _, _, _, _, _ => trivial
  | .tuple ps, x, _, hm, h => Pats.ok_match ps x hm h
  | .ctor v ps, x, _, hm, h => by
    simp only [Pat.match, Option.bind_eq_some_iff] at hm
    obtain ⟨y, hy, hm⟩ := hm
    exact Pats.ok_match ps y hm (Alts.ok_proj x v hy h.2)
  | .as p, x, _, hm, h => by
    simp only [Pat.match, Option.map_eq_some_iff] at hm
    obtain ⟨δ, hδ, rfl⟩ := hm
    exact Dens.ok_append (b := [t]) δ (x, ()) (Pat.ok_match p x hδ h) ⟨h, trivial⟩
theorem Pats.ok_match {ts : List Ty} {Δ : List Ty} : (ps : Pats ts Δ) → (xs : Ty.dens ts) → {δ : Ty.dens Δ} →
    Pats.match ps xs = some δ → Oks i okV ts xs → Oks i okV Δ δ
  | .nil, (), _, _, _ => trivial
  | .cons p ps, (x, xs), _, hm, h => by
    simp only [Pats.match, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    exact Dens.ok_append a b (Pat.ok_match p x ha h.1) (Pats.ok_match ps xs hb h.2)
end

end

/-- Whether a function is `request_command` or `request_query`: the request's `on_answer` runs in a later step. -/
def requestPrim {G Γ ps : List Ty} {r : Ty} (f : Expr G Γ (.fn ps r)) : Bool :=
  match f with
  | .prim p _ _ => p == .requestCommand || p == .requestQuery
  | _ => false

section
variable {G : List Ty} (i : Nat) (tbl : List (List Nat))

-- A global's position is below the table's length, so the empty list is never read.
set_option linter.tazuna.silentDefault false in
mutual
/-- The constructors of the declaration `i` an expression can build when it runs, by `tbl` for each global: those
written in it (a record update builds the type's one constructor), nested functions included, except in the
arguments of a request. -/
def Expr.evs {Γ : List Ty} {t : Ty} : Expr G Γ t → List Nat
  | .int _ | .str _ | .var _ | .prim .. => []
  | .global v => tbl.getD v.idx []
  | @Expr.ctor _ _ j _ _ v es => (if j = i then [v.val] else []) ++ Exprs.evs es
  | .tuple es => Exprs.evs es
  | .field _ _ _ e | .index e _ | .not e | .neg e | .lam e => Expr.evs e
  | @Expr.update _ _ j _ _ e p => (if j = i then [0] else []) ++ Expr.evs e ++ Patch.evs p
  | .call f args => if requestPrim f then [] else Expr.evs f ++ Exprs.evs args
  | .let_ e body | .bin _ e body => Expr.evs e ++ Expr.evs body
  | .case e cs _ => Expr.evs e ++ Clauses.evs cs
  | .list items => Items.evs items
  | .close _ env _ _ body | .closeEffect _ env _ _ body => Exprs.evs env ++ Expr.evs body
def Exprs.evs {Γ ts : List Ty} : Exprs G Γ ts → List Nat
  | .nil => []
  | .cons e es => Expr.evs e ++ Exprs.evs es
def Items.evs {Γ : List Ty} {t : Ty} : Items G Γ t → List Nat
  | .nil => []
  | .cons e es => Expr.evs e ++ Items.evs es
def Patch.evs {Γ ts : List Ty} : Patch G Γ ts → List Nat
  | .nil => []
  | .keep rest => Patch.evs rest
  | .set e rest => Expr.evs e ++ Patch.evs rest
def Clauses.evs {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List Nat
  | .nil => []
  | .cons _ body rest => Expr.evs body ++ Clauses.evs rest
  | .guarded _ g body rest => Expr.evs g ++ Expr.evs body ++ Clauses.evs rest
end

end

/-- For each global, innermost first, the constructors of the declaration `i` its body can build when it runs. -/
def Defs.evs (i : Nat) : {G : List Ty} → Defs G → List (List Nat)
  | [], .nil => []
  | _ :: _, .snoc defs _ body => body.evs i (defs.evs i) :: defs.evs i

-- A global's position is below the table's length, so the empty list is never read.
set_option linter.tazuna.silentDefault false in
/-- The constructors of the declaration `i` the global at position `k` can build when it runs. -/
def Defs.evsAt (i : Nat) {G : List Ty} (D : Defs G) (k : Nat) : List Nat := (D.evs i).getD k []

/-- The constructors of the declaration `i` a kept function can build when it runs. -/
def Fun.evs {t : Ty} (i : Nat) (f : Fun t) : List Nat := f.body.evs i (f.defs.evs i)

/-- The constructors of the declaration `i` a kept function that returns effects can build when it runs. -/
def EffectFun.evs {ps : List Ty} {r : Ty} (i : Nat) (f : EffectFun ps r) : List Nat := f.body.evs i (f.defs.evs i)

section
variable {i : Nat} {okV : Nat → Prop}

theorem ok_insert {k v : Ty} (key : k.den) (val : v.den) (t : (Ty.table k v).den) (hk : Ok i okV k key)
    (hv : Ok i okV v val) (ht : ∀ e ∈ Ty.entries t, Ok i okV k e.1 ∧ Ok i okV v e.2) :
    ∀ e ∈ Ty.entries (Builtin.tableInsert key val t), Ok i okV k e.1 ∧ Ok i okV v e.2 := by
  intro e he
  simp only [Ty.entries, Builtin.tableInsert, Builtin.tableRemove, List.mem_append, List.mem_filter,
    List.mem_singleton] at he
  rcases he with ⟨he, -⟩ | rfl
  · exact ht e he
  · exact ⟨hk, hv⟩

/-- Every built-in keeps `Ok`: it builds only the prelude's types and requests, and what else it returns its arguments
hold. -/
theorem Prim.den_ok (hi : 15 ≤ i) (p : Prim) (args : List Ty) (h : p.ok args = true) :
    Ok i okV (p.ty.inst args) (p.den args h) := by
  have hne : ∀ j, j < 15 → ∀ (Q : Prop), j = i → Q := fun j hj Q e => absurd e (by omega)
  cases p
  all_goals simp only [Prim.ty, Prim.sig, List.map, Ty.inst, Ty.insts, Ty.instss, Ty.bool]
  all_goals first
    | exact fun _ _ => ok_free _ (by simp [Ty.mentions, Ty.mentionsL, Ty.mentionsLL]; omega) _
    | (simp only [Ok]; intro _ _; trivial)
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
    refine ⟨hne 2 (by omega) _, ?_⟩
    change OkAlts i okV _ (Ty.ofPick (Builtin.pick _ (fun x => f (x, ())) xs))
    cases hp : Builtin.pick _ (fun x => f (x, ())) xs with
    | ok w => exact ⟨hb w (pick_mem _ _ _ hp), trivial⟩
    | error b => cases b <;> exact ⟨⟨hne 4 (by omega) _, trivial⟩, trivial⟩
  case tableNew => intro _ _ e he; cases he
  case tableFromList =>
    rintro ⟨pairs, ⟨⟩⟩ ⟨hp, -⟩
    dsimp only [Prim.den]
    refine foldl_inv (fun t => ∀ e ∈ Ty.entries t, Ok i okV _ e.1 ∧ Ok i okV _ e.2) (Oks i okV [_, _]) _ ?_ pairs _ hp
      (fun e he => by cases he)
    rintro t ⟨k, v, ⟨⟩⟩ ht hkv
    exact ok_insert k v t hkv.1 hkv.2.1 ht
  case tableInsert =>
    rintro ⟨t, k, v, ⟨⟩⟩ ⟨ht, hk, hv, -⟩
    exact ok_insert k v t hk hv ht
  case tableRemove =>
    rintro ⟨t, k, ⟨⟩⟩ ⟨ht, -, -⟩ e he
    exact ht e (List.mem_filter.1 he).1
  case tableGet =>
    rintro ⟨t, k, ⟨⟩⟩ ⟨ht, -, -⟩
    refine ⟨hne 3 (by omega) _, ?_⟩
    change OkAlts i okV _ (match lookupBy _ k t.1 with | .some v => Ty.some v | .none => Ty.none)
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
    have key : ∀ c : Bool, Ok i okV (Ty.inst args ((Ty.param 0).result (Ty.param 1)))
        (if c = true then next () else Ty.error rej) := fun c => by
      cases c
      · exact ⟨hne 2 (by omega) _, hr, trivial⟩
      · exact hn () trivial
    exact key _
  case tableLookup =>
    rintro ⟨t, k, rej, next, ⟨⟩⟩ ⟨ht, -, hr, hn, -⟩
    change Ok i okV _ (match lookupBy _ k t.1 with | .some v => next (v, ()) | .none => Ty.error rej)
    cases hl : lookupBy _ k t.1 with
    | some v =>
      obtain ⟨e, he, rfl⟩ := lookupBy_mem _ _ _ hl
      exact hn (e.2, ()) ⟨(ht e he).2, trivial⟩
    | none => exact ⟨hne 2 (by omega) _, hr, trivial⟩
  case sendCommand =>
    rintro ⟨c, input, oa, ⟨⟩⟩ ⟨-, -, ho, -⟩
    intro hj y z hz
    have hm : Ty.mentionsL i [Ty.result Ty.nil ((Ty.param 4).inst args)] = false := by
      simp only [Ty.mentionsL, Ty.mentions, Ty.result, Ty.nil, Ty.mentionsLL, hj]; simp; omega
    exact ho y (oks_free _ hm y) z hz
  case sendQuery =>
    rintro ⟨q, input, oa, ⟨⟩⟩ ⟨-, -, ho, -⟩
    intro hj y z hz
    have hm : Ty.mentionsL i [(Ty.param 4).inst args] = false := by simp only [Ty.mentionsL, hj]; rfl
    exact ho y (oks_free _ hm y) z hz
end

section
variable {i : Nat} {okV : Nat → Prop} {G : List Ty} (D : Defs G) (g : Ty.dens G)

theorem requestPrim_ok {Γ ps : List Ty} {r : Ty} (f : Expr G Γ (.fn ps r)) (hf : requestPrim f = true)
    (ρ : Ty.dens Γ) (xs : Ty.dens ps) : Ok i okV r (f.eval D g ρ xs) := by
  unfold requestPrim at hf
  split at hf
  · rename_i _ _ q targs hq
    cases q <;> (try (exfalso; revert hf; decide))
    all_goals
      obtain ⟨a, b, c, ⟨⟩⟩ := xs
      exact trivial
  · cases hf

end

theorem BinOp.free {i : Nat} (hi : 15 ≤ i) {a b c : Ty} : BinOp a b c → c.mentions i = false
  | .add | .sub | .mul | .div | .mod | .concat => rfl
  | .lt | .le | .gt | .ge | .and | .or | .eq _ | .ne _ => by
    simp [Ty.bool, Ty.mentions, Ty.mentionsL, Ty.mentionsLL]; omega

section
variable {i : Nat} {okV : Nat → Prop} (hi : 15 ≤ i) {G : List Ty} (D : Defs G)
  (hg : ∀ {t : Ty} (v : Var G t), (∀ k ∈ D.evsAt i v.idx, okV k) → Ok i okV t (v.get D.eval))
include hi hg
set_option linter.unusedSectionVars false

mutual
/-- Evaluation keeps `Ok` when every constructor of the declaration the expression can build is allowed and the
variables are `Ok`. -/
theorem Expr.ok {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → (∀ k ∈ e.evs i (D.evs i), okV k) → (ρ : Ty.dens Γ) →
    Oks i okV Γ ρ → Ok i okV t (e.eval D D.eval ρ)
  | .int _, _, _, _ | .str _, _, _, _ => trivial
  | .var v, _, ρ, hρ => Var.ok v ρ hρ
  | .global v, hs, _, _ => hg v hs
  | @Expr.ctor _ _ j _ _ v es, hs, ρ, hρ => by
    refine ⟨fun e => ?_, Alts.okAlts_inj v _ (Exprs.ok es (sub_r hs) ρ hρ)⟩
    simp only [Expr.eval, Alts.index_inj]
    exact hs v.val (List.mem_append_left _ (by simp [e]))
  | .field _ k hk e, hs, ρ, hρ => by
    have he := Alts.ok_view _ (Expr.ok e hs ρ hρ).2
    simp only [Expr.eval]
    exact Dens.ok_field _ k _ he
  | .index e k, hs, ρ, hρ => Dens.ok_get _ k (Expr.ok e hs ρ hρ)
  | @Expr.update _ _ j _ _ e p, hs, ρ, hρ => by
    have hx := Expr.ok e (sub_r (sub_l hs)) ρ hρ
    simp only [Expr.eval]
    refine ⟨fun h => ?_, Alts.okAlts_inj ⟨0, by simp⟩ _ (Patch.ok p (sub_r hs) ρ hρ _ ?_)⟩
    · rw [Alts.index_inj]
      exact hs 0 (List.mem_append_left _ (List.mem_append_left _ (by simp [h])))
    · revert hx
      generalize Expr.eval D D.eval e ρ = x
      match x with
      | .inl y => exact fun h => h.2
  | .call f args, hs, ρ, hρ => by
    simp only [Expr.evs] at hs
    split at hs
    · exact requestPrim_ok D D.eval f (by assumption) ρ _
    · exact (Expr.ok f (sub_l hs) ρ hρ) _ (Exprs.ok args (sub_r hs) ρ hρ)
  | .lam body, hs, ρ, hρ => fun xs hxs => Expr.ok body hs _ (Dens.ok_append xs ρ hxs hρ)
  | .let_ e body, hs, ρ, hρ => Expr.ok body (sub_r hs) _ ⟨Expr.ok e (sub_l hs) ρ hρ, hρ⟩
  | .case e cs hc, hs, ρ, hρ => Clauses.ok cs (sub_r hs) ρ hρ _ (Expr.ok e (sub_l hs) ρ hρ) _
  | .list items, hs, ρ, hρ => Items.ok items hs ρ hρ
  | .tuple es, hs, ρ, hρ => Exprs.ok es hs ρ hρ
  | .bin op _ _, _, _, _ => ok_free _ (op.free hi) _
  | .not _, _, _, _ => ok_free _ (by simp [Ty.bool, Ty.mentions, Ty.mentionsL, Ty.mentionsLL]; omega) _
  | .neg _, _, _, _ => trivial
  | .prim p args h, _, _, _ => Prim.den_ok hi p args h
  | .close site env hΓ ht body, hs, ρ, hρ => by
    show Ok i okV _ (Expr.eval D D.eval body (Ty.up _ hΓ (Ty.down _ hΓ (Exprs.eval D D.eval env ρ))))
    erw [Ty.up_down]
    exact Expr.ok body (sub_r hs) _ (Exprs.ok env (sub_l hs) ρ hρ)
  | .closeEffect _ env hΓ _ body, hs, ρ, hρ => by
    intro xs hxs
    show Ok i okV _ (Expr.eval D D.eval body (Ty.up _ hΓ (Ty.down _ hΓ (Exprs.eval D D.eval env ρ))) xs)
    erw [Ty.up_down]
    exact Expr.ok body (sub_r hs) _ (Exprs.ok env (sub_l hs) ρ hρ) xs hxs
theorem Exprs.ok {Γ ts : List Ty} : (es : Exprs G Γ ts) → (∀ k ∈ Exprs.evs i (D.evs i) es, okV k) →
    (ρ : Ty.dens Γ) → Oks i okV Γ ρ → Oks i okV ts (Exprs.eval D D.eval es ρ)
  | .nil, _, _, _ => trivial
  | .cons e es, hs, ρ, hρ => ⟨Expr.ok e (sub_l hs) ρ hρ, Exprs.ok es (sub_r hs) ρ hρ⟩
theorem Items.ok {Γ : List Ty} {t : Ty} : (items : Items G Γ t) → (∀ k ∈ Items.evs i (D.evs i) items, okV k) →
    (ρ : Ty.dens Γ) → Oks i okV Γ ρ → ∀ x ∈ Items.eval D D.eval items ρ, Ok i okV t x
  | .nil, _, _, _, _, hx => by cases hx
  | .cons e es, hs, ρ, hρ, x, hx => by
    cases hx with
    | head => exact Expr.ok e (sub_l hs) ρ hρ
    | tail _ hx => exact Items.ok es (sub_r hs) ρ hρ x hx
theorem Patch.ok {Γ ts : List Ty} : (p : Patch G Γ ts) → (∀ k ∈ Patch.evs i (D.evs i) p, okV k) →
    (ρ : Ty.dens Γ) → Oks i okV Γ ρ → (xs : Ty.dens ts) → Oks i okV ts xs →
    Oks i okV ts (Patch.eval D D.eval p ρ xs)
  | .nil, _, _, _, (), _ => trivial
  | .keep rest, hs, ρ, hρ, (_, xs), hx => ⟨hx.1, Patch.ok rest hs ρ hρ xs hx.2⟩
  | .set e rest, hs, ρ, hρ, (_, xs), hx => ⟨Expr.ok e (sub_l hs) ρ hρ, Patch.ok rest (sub_r hs) ρ hρ xs hx.2⟩
theorem Clauses.ok {Γ : List Ty} {t r : Ty} {sh : List Shape} : (cs : Clauses G Γ t r sh) →
    (∀ k ∈ Clauses.evs i (D.evs i) cs, okV k) → (ρ : Ty.dens Γ) → Oks i okV Γ ρ → (x : t.den) → Ok i okV t x →
    (h : ∃ s ∈ sh, Shape.Matches t s x) → Ok i okV r (Clauses.eval D D.eval cs ρ x h)
  | .nil, _, _, _, _, _, h => False.elim (by simp at h)
  | .cons p body rest, hs, ρ, hρ, x, hx, h => by
    simp only [Clauses.eval]
    split
    · rename_i δ hm
      exact Expr.ok body (sub_l hs) _ (Dens.ok_append δ ρ (Pat.ok_match p x hm hx) hρ)
    · exact Clauses.ok rest (sub_r hs) ρ hρ x hx _
  | .guarded p guard body rest, hs, ρ, hρ, x, hx, h => by
    simp only [Clauses.eval]
    split
    · rename_i δ hm
      split
      · exact Expr.ok body (sub_r (sub_l hs)) _ (Dens.ok_append δ ρ (Pat.ok_match p x hm hx) hρ)
      · exact Clauses.ok rest (sub_r hs) ρ hρ x hx h
    · exact Clauses.ok rest (sub_r hs) ρ hρ x hx h
end

end

/-- Every global is `Ok` when every constructor of the declaration its body can build is allowed. -/
theorem Defs.ok {i : Nat} {okV : Nat → Prop} (hi : 15 ≤ i) : {G : List Ty} → (D : Defs G) → {t : Ty} →
    (v : Var G t) → (∀ k ∈ D.evsAt i v.idx, okV k) → Ok i okV t (v.get D.eval)
  | _ :: _, .snoc defs _ body, _, .here, hu => Expr.ok hi defs (fun v h => Defs.ok hi defs v h) body hu () trivial
  | _ :: _, .snoc defs _ _, _, .there v, hu => Defs.ok hi defs v hu

/-- A kept function is `Ok` when every constructor of the declaration it can build is allowed and the values it
captured are `Ok`. -/
theorem Fun.ok_eval {i : Nat} {okV : Nat → Prop} (hi : 15 ≤ i) {t : Ty} (f : Fun t) (hf : ∀ k ∈ f.evs i, okV k)
    (henv : Oks i okV f.Γ (Ty.up _ f.hΓ f.env)) : Ok i okV t f.eval :=
  Expr.ok hi f.defs (Defs.ok hi f.defs) f.body hf _ henv

/-- So is a kept function that returns effects. -/
theorem EffectFun.ok_eval {i : Nat} {okV : Nat → Prop} (hi : 15 ≤ i) {ps : List Ty} {r : Ty} (f : EffectFun ps r)
    (hf : ∀ k ∈ f.evs i, okV k) (henv : Oks i okV f.Γ (Ty.up _ f.hΓ f.env)) : Ok i okV (.fn ps r) f.eval :=
  Expr.ok hi f.defs (Defs.ok hi f.defs) f.body hf _ henv

/-! The step. -/

/-- Whether an origin is an outside caller's. -/
def isOutside {c : Ty} : (Ty.origin c).den0 → Bool
  | .inl _ => true
  | .inr _ => false

namespace ServiceV
variable (v : ServiceV)

/-- Whether the command runs when the service sends it itself: `Own` is among its callers. -/
def ownRuns (x : CommandV v.records v.event v.caller) : Bool :=
  x.callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 Step.own)

/-- Whether no value a step starts from can hold a value of the declaration `i`: not the records, a caller, a machine's
key or state, a command's input or rejection, a query's output, a subscription's event, nor a value the kept
functions of the step captured. -/
def quiet (i : Nat) : Bool :=
  !v.records.mentions i && !v.caller.mentions i &&
  v.machines.all (fun m => !m.key.mentions i && !m.state.mentions i && !(Ty.tuple m.effect.Γ).mentions i) &&
  v.commands.all (fun x => !x.input.mentions i && !x.rejection.mentions i && !(Ty.tuple x.decide.Γ).mentions i) &&
  v.queries.all (fun q => !q.output.mentions i) &&
  v.reactions.all (fun x => !(Ty.tuple x.react.Γ).mentions i) &&
  v.subscribes.all (fun sub => !sub.event.mentions i && !(Ty.tuple sub.wrap.Γ).mentions i)

/-- The constructors of the declaration `i` the cascade can build: each machine's `effect`, each reaction, and each
command the service runs as `Own`. -/
def cascadeEvs (i : Nat) : List Nat :=
  v.machines.flatMap (·.effect.evs i) ++ v.reactions.flatMap (·.react.evs i) ++
    (v.commands.filter v.ownRuns).flatMap (·.decide.evs i)

end ServiceV

/-- `ServiceV.quiet` as facts. -/
structure Quiet (i : Nat) (v : ServiceV) : Prop where
  records : v.records.mentions i = false
  caller : v.caller.mentions i = false
  machines : ∀ m ∈ v.machines,
    m.key.mentions i = false ∧ m.state.mentions i = false ∧ (Ty.tuple m.effect.Γ).mentions i = false
  commands : ∀ x ∈ v.commands,
    x.input.mentions i = false ∧ x.rejection.mentions i = false ∧ (Ty.tuple x.decide.Γ).mentions i = false
  queries : ∀ q ∈ v.queries, q.output.mentions i = false
  reactions : ∀ x ∈ v.reactions, (Ty.tuple x.react.Γ).mentions i = false
  subscribes : ∀ sub ∈ v.subscribes, sub.event.mentions i = false ∧ (Ty.tuple sub.wrap.Γ).mentions i = false

theorem quiet_facts {v : ServiceV} {i : Nat} (h : v.quiet i = true) : Quiet i v := by
  simp only [ServiceV.quiet, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, fun m hm => by have := h3 m hm; simp_all, fun x hx => by have := h4 x hx; simp_all,
    fun q hq => by have := h5 q hq; simp_all, fun x hx => by have := h6 x hx; simp_all,
    fun x hx => by have := h7 x hx; simp_all⟩

section
variable {i : Nat} {okV : Nat → Prop}

theorem altIndex_up {k : Nat} {a : List Ty} : (vs : List (List Ty)) → (h : (Ty.adt k a vs).isData = true) →
    (x : (Ty.adt k a vs).den0) → Alts.index (Ty.up _ h x) = altIndex vs x
  | [], _, x => nomatch x
  | fs :: vs, h, .inl x => by
    have hfs : (Ty.tuple fs).isData = true := by simp_all [Ty.isData, Ty.isDatass]
    rw [Ty.up_inl k a fs vs h hfs x]; rfl
  | _ :: vs, h, .inr y => by
    have hvs : (Ty.adt k a vs).isData = true := by simp_all [Ty.isData, Ty.isDatass]
    rw [Ty.up_inr k a _ vs h hvs y]
    have := altIndex_up vs hvs y
    simp only [Alts.index, Alts.view] at this ⊢
    simp only [altIndex, this]

/-- An allowed value of a custom type of the declaration `i` is built with an allowed constructor. -/
theorem ok_variant (T : List TypeDecl) {V : Option String} {ns : List Nat} : (t : Ty) → (h : t.isData = true) →
    (x : t.den0) → (∃ a vs, t = .adt i a vs) → Ok i (· ∈ ns) t (Ty.up t h x) →
    (ns.any fun n => variantName T i n == V) = false → variantOf T t x ≠ V
  | .adt j a vs, h, x, ⟨_, _, he⟩, hok, hns, hv => by
    cases he
    have hm := hok.1 rfl
    rw [altIndex_up vs h x] at hm
    simp only [variantOf] at hv
    have := List.any_eq_false.1 hns _ hm
    simp [hv] at this

theorem toOption_ok {t : Ty} (y : (Ty.option t).den) (hy : Ok i okV (Ty.option t) y) {x : t.den}
    (h : Ty.toOption y = some x) : Ok i okV t x := by
  rcases y with ⟨y, ⟨⟩⟩ | y
  · simp only [Ty.toOption, Option.some.injEq] at h; subst h; exact hy.2.1
  · simp [Ty.toOption] at h

theorem oks_up_cons {t : Ty} {ts : List Ty} (h : (Ty.tuple (t :: ts)).isData = true) (x : t.den0)
    (xs : (Ty.tuple ts).den0) (hx : ∀ h' : t.isData = true, Ok i okV t (Ty.up t h' x))
    (hxs : ∀ h' : (Ty.tuple ts).isData = true, Oks i okV ts (Ty.up (.tuple ts) h' xs)) :
    Oks i okV (t :: ts) (Ty.up (.tuple (t :: ts)) h (x, xs)) := by
  have ht : t.isData = true := by simp_all [Ty.isData, Ty.isDatas]
  have hts : (Ty.tuple ts).isData = true := by simp_all [Ty.isData, Ty.isDatas]
  erw [Ty.up_tuple t ts h ht hts]
  exact ⟨hx ht, hxs hts⟩

/-- The list a data function returns is the list of its items, each brought down. -/
theorem down_list {t : Ty} (h : (Ty.list t).isData = true) (ht : t.isData = true) (xs : List t.den) :
    Ty.down (.list t) h xs = xs.map (Ty.down t ht) := by
  unfold Ty.down; exact cast_list _ _ xs

/-- The events a kept function returns, where what it means returns allowed ones at the arguments. -/
theorem fn_events {ps : List Ty} {e : Ty} (f : Fun (.fn ps (.list e))) (hps : (Ty.tuple ps).isData = true)
    (xs : (Ty.tuple ps).den0) (hf : ∀ z ∈ Ty.listItems (f.eval (Ty.up _ hps xs)), Ok i okV e z) :
    ∀ ev ∈ @id (List e.den0) (f.fn xs), ∀ h : e.isData = true, Ok i okV e (Ty.up e h ev) := by
  intro ev hev he
  have hr : (Ty.list e).isData = true := he
  have e1 : @id (List e.den0) (f.fn xs) = (@id (List e.den) (f.eval (Ty.up _ hps xs))).map (Ty.down e he) := by
    rw [Fun.fn_app f hps hr]
    exact down_list hr he _
  rw [e1] at hev
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hev
  rw [Ty.up_down]
  exact hf z hz

end

namespace Step

variable (T : List TypeDecl) {v : ServiceV} {i : Nat} {okV : Nat → Prop}

/-- An effect whose `on_answer` returns only allowed events. -/
abbrev EffOk (i : Nat) (okV : Nat → Prop) (eff : EffectV v.event) : Prop := Ok i okV (.dsl .effect [v.event]) eff

/-- What a step in progress keeps: every event it applied is allowed, every own effect waiting returns only allowed
events, and (where `b`) no out line goes out before an event. -/
structure AccOk (i : Nat) (okV : Nat → Prop) (b : Bool) (a : Acc v) : Prop where
  events : ∀ ev ∈ a.events, ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)
  own : ∀ o ∈ a.own, EffOk i okV o.effect
  out : b = true → a.out = [] ∨ a.events ≠ []

theorem accOk_start (b : Bool) (s : State v) : AccOk i okV b ({ state := s } : Acc v) :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ => .inl rfl⟩

theorem start_events (a : Acc v) (effs : List (Sender × EffectV v.event)) {a' : Acc v} (h : start a effs = .ok a') :
    a'.events = a.events := by
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; rw [h]
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      rw [ih a1 h]
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · intro h1; cases h1; rfl
      | command => intro h1; cases h1; rfl
      | query => intro h1; cases h1; rfl

theorem start_ok {b : Bool} (a : Acc v) (effs : List (Sender × EffectV v.event)) (ha : AccOk i okV b a)
    (he : ∀ x ∈ effs, EffOk i okV x.2) (hb : b = true → a.events ≠ []) {a' : Acc v} (h : start a effs = .ok a') :
    AccOk i okV b a' := by
  have hev := start_events a effs h
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      have h1e : a1.events = a.events := by
        revert h1
        cases eff with
        | request r =>
          simp only
          split
          · intro h1; cases h1
          · intro h1; cases h1; rfl
        | command => intro h1; cases h1; rfl
        | query => intro h1; cases h1; rfl
      refine ih a1 ?_ (fun y hy => he y (by simp [hy])) (fun hb' => h1e ▸ hb hb') h (by rw [hev, h1e])
      have hx : EffOk i okV eff := he (snd, eff) (by simp)
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · intro h1
          cases h1
          exact ⟨ha.events, ha.own, fun hb' => .inr (hb hb')⟩
      | command =>
        intro h1; cases h1
        refine ⟨ha.events, fun o ho => ?_, ha.out⟩
        rcases List.mem_append.1 ho with ho | ho
        · exact ha.own o ho
        · simp only [List.mem_singleton] at ho; subst ho; exact hx
      | query =>
        intro h1; cases h1
        refine ⟨ha.events, fun o ho => ?_, ha.out⟩
        rcases List.mem_append.1 ho with ho | ho
        · exact ha.own o ho
        · simp only [List.mem_singleton] at ho; subst ho; exact hx

section
variable (hi : 15 ≤ i) (hq : Quiet i v) (hc : ∀ k ∈ v.cascadeEvs i, okV k)
include hi hq hc

theorem enter_ok {m : MachineV v.records v.event} (hm : m ∈ v.machines) (records : v.records.den0) (now : Int)
    (key : m.key.den0) (st : m.state.den0) : ∀ x ∈ (enter m records now key st).2, EffOk i okV x.2 := by
  intro x hx
  simp only [enter, List.mem_map, Option.mem_toList] at hx
  obtain ⟨eff, heff, rfl⟩ := hx
  obtain ⟨hk, hs, hΓ⟩ := hq.machines m hm
  have hf := EffectFun.ok_eval (okV := okV) hi m.effect (fun k hk' => hc k (by
    simp only [ServiceV.cascadeEvs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl ⟨m, hm, hk'⟩))) (oks_free _ hΓ _)
  have hy := hf (Ty.up _ m.effect.hps (.inl (key, st, records, now, ()), ())) (oks_free _ (by
    simp [Ty.machineCtx, Ty.mentionsL, Ty.mentions, Ty.mentionsLL, hk, hs, hq.records]; omega) _)
  exact toOption_ok _ hy heff

theorem reaction_ok {x : ReactionV v.records v.event} (hx : x ∈ v.reactions) (ev : v.event.den0)
    (hev : ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) (records : v.records.den0) (now : Int) :
    ∀ eff ∈ x.effectsAt ev records now, EffOk i okV eff := by
  have hf := EffectFun.ok_eval (okV := okV) hi x.react (fun k hk' => hc k (by
    simp only [ServiceV.cascadeEvs, List.mem_append, List.mem_flatMap]
    exact .inl (.inr ⟨x, hx, hk'⟩))) (oks_free _ (hq.reactions x hx) _)
  refine hf _ (oks_up_cons _ _ _ (fun _ => ok_free _ (by
    simp [Ty.reactionCtx, Ty.mentionsL, Ty.mentions, Ty.mentionsLL, hq.records]; omega) _)
    (fun _ => oks_up_cons _ _ _ hev (fun _ => trivial)))

theorem react_ok (s : State v) (ev : v.event.den0)
    (hev : ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) :
    ∀ x ∈ (react T s ev).2, EffOk i okV x.2 := by
  let records := v.apply.fn (.inl (s.records, s.now, ()), ev, ())
  have hm := mem_reactMachines_effs T records s.now ev s.machines
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨sm, hsm, h⟩ := hm x h
    simp only [machineStep, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨k, -, rfl⟩, h⟩ := h
    revert h
    unfold reactKey
    split
    · split
      · exact enter_ok hi hq hc (PerMachine.fst_mem hsm) _ _ _ _ x
      · intro h; cases h
    · exact enter_ok hi hq hc (PerMachine.fst_mem hsm) _ _ _ _ x
  · simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨y, hy, eff, heff, rfl⟩ := h
    exact reaction_ok hi hq hc hy ev hev records s.now eff heff

theorem applyEvents_ok {b : Bool} (evs : List v.event.den0)
    (hevs : ∀ ev ∈ evs, ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) :
    (a : Acc v) → AccOk i okV b a → {a' : Acc v} → applyEvents T a evs = .ok a' → AccOk i okV b a' := by
  induction evs with
  | nil => intro a ha a' h; simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons ev evs ih =>
    intro a ha a' h
    simp only [applyEvents, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      refine ih (fun y hy => hevs y (by simp [hy])) a1 ?_ h
      refine start_ok _ _ ?_ (react_ok T hi hq hc a.state ev (hevs ev (by simp))) (fun _ => by simp) h1
      refine ⟨fun e he => ?_, ha.own, fun _ => .inr (by simp)⟩
      rcases List.mem_append.1 he with he | he
      · exact ha.events e he
      · simp only [List.mem_singleton] at he; subst he; exact hevs _ (by simp)

omit hi hq hc in
/-- The events a command's `decide` returns are allowed. -/
theorem result_events {ps : List Ty} {e j : Ty} (f : Fun (.fn ps (.result (.list e) j)))
    (hps : (Ty.tuple ps).isData = true) (xs : (Ty.tuple ps).den0)
    (hf : Ok i okV (.result (.list e) j) (f.eval (Ty.up _ hps xs))) {evs : List e.den0}
    (h : f.fn xs = .inl (evs, ())) : ∀ ev ∈ evs, ∀ he : e.isData = true, Ok i okV e (Ty.up e he ev) := by
  have hr : (Ty.result (.list e) j).isData = true := by
    have := f.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.2
  have hfs : (Ty.tuple [.list e]).isData = true := by simp_all [Ty.result, Ty.isData, Ty.isDatass, Ty.isDatas]
  have hy : f.eval (Ty.up _ hps xs) = Ty.up _ hr (.inl (evs, ())) := by
    rw [← h, Fun.fn_app f hps hr, Ty.up_down]
  rw [hy] at hf
  have hl : (Ty.list e).isData = true := by simp_all [Ty.isData, Ty.isDatas]
  erw [Ty.up_inl 2 _ [.list e] [[j]] hr hfs, Ty.up_tuple (.list e) [] hfs hl rfl] at hf
  intro ev hev he
  have := hf.2.1
  erw [Ty.up_list e hl he] at this
  exact this _ (List.mem_map_of_mem hev)

theorem execCommand_ok {b : Bool} (a : Acc v) (ha : AccOk i okV b a) (x : CommandV v.records v.event v.caller)
    (hx : x ∈ v.commands) (hd : ∀ k ∈ x.decide.evs i, okV k) (caller : (Ty.origin v.caller).den0)
    (input : x.input.den0) {r : Ran v x.rejection} (h : execCommand T a x caller input = .ok r) (a' : Acc v)
    (ha' : r = .accepted a' ∨ ∃ j, r = .rejected a' j) : AccOk i okV b a' := by
  obtain ⟨hin, -, hΓ⟩ := hq.commands x hx
  have hf := Fun.ok_eval (okV := okV) hi x.decide hd (oks_free _ hΓ _)
  have hps : (Ty.tuple [Ty.ctx v.records x.input v.caller]).isData = true := by
    have := x.decide.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
  have ha1 : AccOk i okV b ({ a with state := { a.state with fresh := a.state.fresh + 1 } } : Acc v) :=
    ⟨ha.events, ha.own, ha.out⟩
  simp only [execCommand] at h
  split at h
  · cases h; rcases ha' with h | ⟨_, h⟩ <;> cases h
  · split at h
    · rename_i evs hdec
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i a2 h2
        split at h
        · cases h
        · cases h
          rcases ha' with h | ⟨_, h⟩ <;> cases h
          refine applyEvents_ok T hi hq hc evs (result_events x.decide hps _ (hf _ (oks_free _ (by
            simp [Ty.ctx, Ty.origin, Ty.mentionsL, Ty.mentions, Ty.mentionsLL, hin, hq.records, hq.caller]; omega) _))
            hdec) _ ha1 h2
    · cases h; rcases ha' with h | ⟨_, h⟩ <;> cases h; exact ha1

theorem runCommand_ok {b : Bool} (a : Acc v) (ha : AccOk i okV b a) (x : CommandV v.records v.event v.caller)
    (hx : x ∈ v.commands) (hd : ∀ k ∈ x.decide.evs i, okV k) (caller : (Ty.origin v.caller).den0)
    (input : x.input.den0) (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event)))
    (hoa : ∀ y, ∀ z ∈ Ty.listItems (onAnswer.eval y), Ok i okV v.event z) {a' : Acc v}
    (h : runCommand T a x caller input onAnswer = .ok a') : AccOk i okV b a' := by
  have hps : (Ty.tuple [Ty.result Ty.nil x.rejection]).isData = true := by
    have := onAnswer.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
  simp only [runCommand, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    have hi1 := execCommand_ok T hi hq hc a ha x hx hd caller input hr
    split at h
    · cases h
    · exact applyEvents_ok T hi hq hc _ (fn_events onAnswer hps _ (hoa _)) _ (hi1 _ (.inl rfl)) h
    · exact applyEvents_ok T hi hq hc _ (fn_events onAnswer hps _ (hoa _)) _ (hi1 _ (.inr ⟨_, rfl⟩)) h

theorem runQuery_ok {b : Bool} (a : Acc v) (ha : AccOk i okV b a) (x : QueryV v.records v.caller)
    (caller : (Ty.origin v.caller).den0) (input : x.input.den0) (onAnswer : Fun (Ty.fn [x.output] (.list v.event)))
    (hoa : ∀ y, ∀ z ∈ Ty.listItems (onAnswer.eval y), Ok i okV v.event z) {a' : Acc v}
    (h : runQuery T a x caller input onAnswer = .ok a') : AccOk i okV b a' := by
  have hps : (Ty.tuple [x.output]).isData = true := by
    have := onAnswer.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
  simp only [runQuery] at h
  split at h
  · cases h
  · refine applyEvents_ok T hi hq hc _ (fn_events onAnswer hps _ (hoa _)) _ ?_ h
    exact ⟨ha.events, ha.own, ha.out⟩

end

/-- A command the service does not run as `Own` is refused when an effect sends it. -/
theorem runCommand_notOwn (a : Acc v) (x : CommandV v.records v.event v.caller) (hx : v.ownRuns x = false)
    (input : x.input.den0) (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) {a' : Acc v}
    (h : runCommand T a x own input onAnswer = .ok a') : False := by
  simp only [runCommand, execCommand, admit, bind, Except.bind] at h
  simp only [ServiceV.ownRuns] at hx
  simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
  cases h

section
variable (hi : 15 ≤ i) (hq : Quiet i v) (hc : ∀ k ∈ v.cascadeEvs i, okV k)
include hi hq hc

theorem runOwn_ok {b : Bool} (a : Acc v) (ha : AccOk i okV b a) (eff : OwnEffectV v.event)
    (he : EffOk i okV eff.effect) {a' : Acc v} (h : runOwn T a eff = .ok a') : AccOk i okV b a' := by
  revert h
  cases eff with
  | command name c i' j value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => intro h; cases h
    | some hc' =>
      generalize hox : ownCommand (v := v) name i' j = ox
      cases ox with
      | none => intro h; cases h
      | some x =>
        obtain ⟨x, hi', hj⟩ := x
        have hmem := ownCommand_mem hox
        subst hj
        intro h
        have hrej := (hq.commands x hmem).2.1
        cases hown : v.ownRuns x with
        | false => exact (runCommand_notOwn T a x hown _ _ h).elim
        | true =>
          refine runCommand_ok T hi hq hc a ha x hmem (fun k hk => hc k ?_) _ _ _ (he hrej) h
          simp only [ServiceV.cascadeEvs, List.mem_append, List.mem_flatMap, List.mem_filter]
          exact .inr ⟨x, ⟨hmem, hown⟩, hk⟩
  | query name c i' o value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => intro h; cases h
    | some hc' =>
      generalize hox : ownQuery (v := v) name i' o = ox
      cases ox with
      | none => intro h; cases h
      | some x =>
        obtain ⟨x, hi', ho⟩ := x
        have hmem := ownQuery_mem hox
        subst ho
        exact fun h => runQuery_ok T hi hq hc a ha x _ _ _ (he (hq.queries x hmem)) h

theorem settle_ok {b : Bool} : (fuel : Nat) → (a : Acc v) → AccOk i okV b a → {a' : Acc v} →
    settle T fuel a = .ok a' → AccOk i okV b a'
  | fuel, a, ha, a', h => by
    unfold settle at h
    split at h
    · simp only [Except.ok.injEq] at h; exact h ▸ ha
    · cases h
    · rename_i eff rest f hown
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i a1 h1
        have hq1 : AccOk i okV b ({ a with own := rest } : Acc v) :=
          ⟨ha.events, fun o ho => ha.own o (by rw [hown]; exact List.mem_cons_of_mem _ ho), ha.out⟩
        exact settle_ok f a1 (runOwn_ok T hi hq hc _ hq1 eff (ha.own eff (by rw [hown]; exact List.mem_cons_self)) h1) h

theorem finish_ok {b : Bool} (s0 : State v) (x : Except Fault (Acc v)) (hx : ∀ a, x = .ok a → AccOk i okV b a)
    (o : Outcome) : (∀ ev ∈ (finish T s0 x o).events, ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) ∧
      (b = true → (finish T s0 x o).out = [] ∨ (finish T s0 x o).events ≠ []) := by
  unfold finish
  split
  · exact ⟨fun _ h => (by cases h), fun _ => .inl rfl⟩
  · rename_i a ha
    split
    · exact ⟨fun _ h => (by cases h), fun _ => .inl rfl⟩
    · cases x with
      | error e => cases ha
      | ok a0 =>
        have h := settle_ok T hi hq hc _ a0 (hx a0 rfl) ha
        exact ⟨h.events, h.out⟩

theorem fire_ok (s : State v) : (fuel : Nat) → {r : State v × List (Sender × EffectV v.event)} →
    fire s fuel = some r → ∀ x ∈ r.2, EffOk i okV x.2
  | 0, _, h => by cases h
  | fuel + 1, r, h => by
    rw [fire] at h
    split at h
    · cases h; intro x hx; cases hx
    · rename_i d _
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
      have h2 := fire_ok { s with machines := (fireMachines s.records s.now d false s.machines).1 } fuel hr
      have hfx := mem_fireMachines_effs s.records s.now d false s.machines
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨ms, hms, k, st, hx⟩ := hfx x hx
        exact enter_ok hi hq hc (PerMachine.fst_mem hms) _ _ _ _ x hx
      · exact h2 x hx

end

/-- What the input's own functions build is allowed: a command's `decide` (unless no outside caller may send it), a
pending request's `on_answer`, which is a site of its answer's type, or a subscription's `wrap`. -/
def EntryOk (P : List AnySite) (i : Nat) (okV : Nat → Prop) : Input v → Prop
  | .command k _ _ =>
    (v.commands.get k).callers.any isOutside = false ∨ ∀ n ∈ (v.commands.get k).decide.evs i, okV n
  | .query .. => True
  | .answer _ ⟨t, _⟩ => t.mentions i = false ∧ ∀ s ∈ sitesOf P (.fn [t] (.list v.event)),
      (Ty.tuple s.1).mentions i = false ∧ ∀ n ∈ s.2.body.evs i (s.2.defs.evs i), okV n
  | .event k _ => ∀ n ∈ (v.subscribes.get k).wrap.evs i, okV n
  | .clock _ => True

/-- Whether the input is a clock line. -/
def _root_.Tazuna.Ir.Input.isClock : Input v → Bool
  | .clock _ => true
  | _ => false

theorem any_outside {c : Ty} (callers : List (Ty.origin c).den0) (h : callers.any isOutside = false) (x : c.den0) :
    callers.any ((Ty.semWith Dsl.base (Ty.origin c)).2 (outside x)) = false := by
  rw [List.any_eq_false] at h ⊢
  intro o ho
  have := h o ho
  rcases o with o | o
  · simp [isOutside] at this
  · simp [outside, Ty.origin, Ty.semWith, Ty.semAltsWith, Sem.sum]

/-- The cone of influence of a step's events: where no value it starts from can hold an event and the functions it
runs build only allowed constructors, every event it applies is allowed, and an out line goes out only after an
event unless the input is a clock line. -/
theorem step_events (hi : 15 ≤ i) (hq : Quiet i v) (hc : ∀ k ∈ v.cascadeEvs i, okV k) {P : List AnySite}
    (s : State v) (hs : Inv P s) (x : Input v) (hx : EntryOk P i okV x) :
    (∀ ev ∈ (step T v s x).events, ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) ∧
      (x.isClock = false → (step T v s x).out = [] ∨ (step T v s x).events ≠ []) := by
  have none_ok : ∀ (r : Result v), r.events = [] → r.out = [] →
      (∀ ev ∈ r.events, ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) ∧
        (x.isClock = false → r.out = [] ∨ r.events ≠ []) := fun r he ho =>
    ⟨fun ev hev => (by rw [he] at hev; cases hev), fun _ => .inl ho⟩
  have fin : ∀ (s0 : State v) (y : Except Fault (Acc v)) (o : Outcome), (∀ a, y = .ok a → AccOk i okV true a) →
      (∀ ev ∈ (finish T s0 y o).events, ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev)) ∧
        (x.isClock = false → (finish T s0 y o).out = [] ∨ (finish T s0 y o).events ≠ []) := fun s0 y o hy =>
    let h := finish_ok T hi hq hc s0 y hy o
    ⟨h.1, fun _ => h.2 rfl⟩
  cases x with
  | command k caller input =>
    have hmem : v.commands.get k ∈ v.commands := List.get_mem _ _
    simp only [step]
    split
    · exact none_ok _ rfl rfl
    · exact none_ok _ rfl rfl
    · exact none_ok _ rfl rfl
    · rename_i a ha
      rcases hx with hx | hx
      · simp only [execCommand, admit, any_outside _ hx] at ha
        cases ha
      · exact fin _ _ _ fun a' h => by
          cases h; exact execCommand_ok T hi hq hc _ (accOk_start true s) _ hmem hx _ _ ha _ (.inl rfl)
  | query k caller input =>
    simp only [step]
    split <;> exact none_ok _ rfl rfl
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step]
    split
    · exact none_ok _ rfl rfl
    · rename_i p hp
      split
      · exact none_ok _ rfl rfl
      · rename_i h _
        split
        · exact none_ok _ rfl rfl
        · refine fin _ _ _ fun a ha => ?_
          have hpm := List.mem_of_find?_eq_some hp
          have hsite := mem_sitesOf_self (hs.reach p hpm).1
          subst h
          obtain ⟨ht, hsites⟩ := hx
          obtain ⟨hΓ, hev⟩ := hsites _ hsite
          have hps : (Ty.tuple [answerTy p.request.output p.request.rejection]).isData = true := by
            have := p.request.onAnswer.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
          have hf := Fun.ok_eval (okV := okV) hi p.request.onAnswer hev (oks_free _ hΓ _)
          exact applyEvents_ok T hi hq hc _ (fn_events _ hps _ (hf _ (oks_free _ (by
            simp only [Ty.mentionsL, ht]; rfl) _))) _ (accOk_start true _) ha
  | event k value =>
    refine fin _ _ _ fun a ha => applyEvents_ok T hi hq hc _ ?_ _ (accOk_start true s) ha
    intro ev hev he
    simp only [List.mem_singleton] at hev
    subst hev
    have hsub : v.subscribes.get k ∈ v.subscribes := List.get_mem _ _
    obtain ⟨hevt, hΓ⟩ := hq.subscribes _ hsub
    have hps : (Ty.tuple [(v.subscribes.get k).event]).isData = true := by
      have := (v.subscribes.get k).wrap.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
    erw [Fun.fn_app _ hps he, Ty.up_down]
    exact Fun.ok_eval hi _ hx (oks_free _ hΓ _) _ (oks_free _ (by simp only [Ty.mentionsL, hevt]; rfl) _)
  | clock time =>
    simp only [step]
    split
    · exact none_ok _ rfl rfl
    · split
      · exact none_ok _ rfl rfl
      · rename_i s' effs hr
        have h := finish_ok T hi hq hc (b := false) s _ (fun a ha =>
          start_ok _ effs (accOk_start false s') (fire_ok hi hq hc _ _ hr) (fun h => by cases h) ha) .accepted
        exact ⟨h.1, fun h' => by cases h'⟩

end Step

end Tazuna.Ir
