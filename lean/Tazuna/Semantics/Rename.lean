import Tazuna.Semantics.Eval
import Tazuna.Semantics.Order
import Tazuna.Semantics.Forall2

/-! Values up to renaming. Ids a step makes and wire ids are names: spec code only compares them, so a run that numbers
them differently is the same run. Two orders of a cascade's steps number them differently, and so do two orders of a
machine's instances when their keys are fresh ids, since the canonical order compares fresh ids by number. `Ty.relWith`
relates two values of a type that are the same once a renaming `R` is applied to the fresh ids in them and bags and
tables are read as multisets, by recursion on the type: functions relate when related arguments give related results,
the logical-relations reading (Plotkin 1973, Reynolds 1983), which is what lets `eval` be proved to preserve the
relation (`Tazuna.Semantics.Equivariance`). The renaming is a pair of partial bijections, on the step counters fresh
ids are made from and on wire ids, so it relates only the names in use, as CompCert's memory injections relate only
allocated blocks; renaming every name uniformly is nominal techniques' equivariance (Pitts 2013). -/

namespace Tazuna.Ir

/-- A partial bijection on numbers: each number relates to at most one, and at most one relates to each. -/
structure PBij where
  rel : Nat → Nat → Prop
  func : ∀ {a b b'}, rel a b → rel a b' → b = b'
  inj : ∀ {a a' b}, rel a b → rel a' b → a = a'

def PBij.inv (p : PBij) : PBij := ⟨fun a b => p.rel b a, fun h h' => p.inj h h', fun h h' => p.func h h'⟩

/-- Each number to itself. -/
def PBij.refl : PBij where
  rel a b := a = b
  func := by rintro _ _ _ rfl rfl; rfl
  inj := by rintro _ _ _ rfl rfl; rfl

/-- A renaming of the names steps make: `ctr` renames the step counters fresh ids are made from, `wire` the wire ids of
requests. -/
structure Ren where
  ctr : PBij
  wire : PBij

def Ren.inv (R : Ren) : Ren := ⟨R.ctr.inv, R.wire.inv⟩

section FreshId

/-- Distinct pairs of a step's counter and an index make distinct ids. -/
theorem freshId_inj {s s' : Nat} {i i' : Int} (h : freshId s i = freshId s' i') : s = s' ∧ i = i' := by
  simpa only [freshId, IdV.fresh.injEq] using h

theorem freshId_ne_named (s : Nat) (i : Int) (n : String) : freshId s i ≠ .named n := by
  simp [freshId]

end FreshId

/-- Ids related by `R`: an id from outside to itself, and the id a step made from counter `c` and index `i` to the id
made from the counter `R` gives `c` and the same index. -/
def IdV.Rel (R : PBij) (a b : IdV) : Prop :=
  (∃ s, a = .named s ∧ b = .named s) ∨ ∃ c c' i, R.rel c c' ∧ a = freshId c i ∧ b = freshId c' i

theorem IdV.rel_inv {R : PBij} {a b : IdV} : IdV.Rel R a b ↔ IdV.Rel R.inv b a := by
  constructor <;> rintro (⟨s, rfl, rfl⟩ | ⟨c, c', i, h, rfl, rfl⟩)
  · exact .inl ⟨s, rfl, rfl⟩
  · exact .inr ⟨c', c, i, h, rfl, rfl⟩
  · exact .inl ⟨s, rfl, rfl⟩
  · exact .inr ⟨c', c, i, h, rfl, rfl⟩

/-- Related ids are equal exactly when the ids they relate to are. -/
theorem IdV.rel_eq {R : PBij} {a b a' b' : IdV} (h : IdV.Rel R a b) (h' : IdV.Rel R a' b') : a = a' ↔ b = b' := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨c, c', i, hc, rfl, rfl⟩ <;>
    rcases h' with ⟨s', rfl, rfl⟩ | ⟨d, d', j, hd, rfl, rfl⟩
  · simp
  · simp [freshId]
  · simp [freshId]
  · constructor
    · intro e; obtain ⟨rfl, rfl⟩ := freshId_inj e; rw [R.func hc hd]
    · intro e; obtain ⟨rfl, rfl⟩ := freshId_inj e; rw [R.inj hc hd]

/-- Lists related as multisets: item by item once the second is reordered. -/
def Multi {α β : Type} (r : α → β → Prop) (xs : List α) (ys : List β) : Prop := ∃ zs, Forall2 r xs zs ∧ zs.Perm ys

section Multi
variable {α β γ δ : Type} {r : α → β → Prop}

theorem forall2_perm_left {as as' : List α} (hp : as.Perm as') {bs : List β} (h : Forall2 r as bs) :
    ∃ bs', bs.Perm bs' ∧ Forall2 r as' bs' := by
  obtain ⟨bs', hp', h'⟩ := forall2_perm (R := fun b a => r a b) hp (forall2_flip h)
  exact ⟨bs', hp'.symm, forall2_flip h'⟩

theorem Multi.of_forall2 {xs : List α} {ys : List β} (h : Forall2 r xs ys) : Multi r xs ys := ⟨ys, h, .refl _⟩

theorem Multi.perm_left {xs xs' : List α} {ys : List β} (hp : xs.Perm xs') : Multi r xs ys → Multi r xs' ys
  | ⟨_, h, hz⟩ => let ⟨zs', hp', h'⟩ := forall2_perm_left hp h; ⟨zs', h', hp'.symm.trans hz⟩

theorem Multi.perm_right {xs : List α} {ys ys' : List β} (hp : ys.Perm ys') : Multi r xs ys → Multi r xs ys'
  | ⟨zs, h, hz⟩ => ⟨zs, h, hz.trans hp⟩

theorem Multi.flip {xs : List α} {ys : List β} : Multi r xs ys → Multi (fun b a => r a b) ys xs
  | ⟨_, h, hz⟩ => (Multi.of_forall2 (forall2_flip h)).perm_left hz

theorem Multi.imp {r' : α → β → Prop} (hr : ∀ a b, r a b → r' a b) {xs : List α} {ys : List β} :
    Multi r xs ys → Multi r' xs ys
  | ⟨zs, h, hz⟩ => ⟨zs, forall2_imp hr h, hz⟩

theorem Multi.length_eq {xs : List α} {ys : List β} : Multi r xs ys → xs.length = ys.length
  | ⟨_, h, hz⟩ => (forall2_length h).trans hz.length_eq

theorem Multi.nil : Multi r ([] : List α) ([] : List β) := ⟨[], trivial, .nil⟩

theorem Multi.cons {a : α} {b : β} {xs : List α} {ys : List β} (hab : r a b) : Multi r xs ys → Multi r (a :: xs) (b :: ys)
  | ⟨zs, h, hz⟩ => ⟨b :: zs, ⟨hab, h⟩, hz.cons b⟩

theorem Multi.append {xs xs' : List α} {ys ys' : List β} : Multi r xs ys → Multi r xs' ys' → Multi r (xs ++ xs') (ys ++ ys')
  | ⟨zs, h, hz⟩, ⟨zs', h', hz'⟩ => ⟨zs ++ zs', forall2_append h h', hz.append hz'⟩

theorem forall2_map2 {r' : γ → δ → Prop} {f : α → γ} {g : β → δ} (hfg : ∀ a b, r a b → r' (f a) (g b)) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → Forall2 r' (xs.map f) (ys.map g)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hab, h⟩ => ⟨hfg _ _ hab, forall2_map2 hfg h⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Multi.map {r' : γ → δ → Prop} {f : α → γ} {g : β → δ} (hfg : ∀ a b, r a b → r' (f a) (g b))
    {xs : List α} {ys : List β} : Multi r xs ys → Multi r' (xs.map f) (ys.map g)
  | ⟨zs, h, hz⟩ => ⟨zs.map g, forall2_map2 hfg h, hz.map g⟩

theorem forall2_filter {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → Forall2 r (xs.filter p) (ys.filter q)
  | [], [], _ => trivial
  | a :: xs, b :: ys, ⟨hab, h⟩ => by
    simp only [List.filter_cons, hpq _ _ hab]
    split
    · exact ⟨hab, forall2_filter hpq h⟩
    · exact forall2_filter hpq h
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Multi.filter {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) {xs : List α} {ys : List β} :
    Multi r xs ys → Multi r (xs.filter p) (ys.filter q)
  | ⟨zs, h, hz⟩ => ⟨zs.filter q, forall2_filter hpq h, hz.filter q⟩

theorem forall2_any {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → xs.any p = ys.any q
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hab, h⟩ => by simp only [List.any_cons, hpq _ _ hab, forall2_any hpq h]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Multi.any_eq {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) {xs : List α} {ys : List β} :
    Multi r xs ys → xs.any p = ys.any q
  | ⟨_, h, hz⟩ => (forall2_any hpq h).trans hz.any_eq

theorem forall2_all_eq {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → xs.all p = ys.all q
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hab, h⟩ => by simp only [List.all_cons, hpq _ _ hab, forall2_all_eq hpq h]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Multi.all_eq {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) {xs : List α} {ys : List β} :
    Multi r xs ys → xs.all p = ys.all q
  | ⟨_, h, hz⟩ => (forall2_all_eq hpq h).trans hz.all_eq

theorem Multi.flatMap {r' : γ → δ → Prop} {f : α → List γ} {g : β → List δ}
    (hfg : ∀ a b, r a b → Multi r' (f a) (g b)) {xs : List α} {ys : List β} :
    Multi r xs ys → Multi r' (xs.flatMap f) (ys.flatMap g)
  | ⟨zs, h, hz⟩ => (go h).perm_right (hz.flatMap_right g)
where
  go : {xs : List α} → {zs : List β} → Forall2 r xs zs → Multi r' (xs.flatMap f) (zs.flatMap g)
    | [], [], _ => Multi.nil
    | _ :: _, _ :: _, ⟨hab, h⟩ => by simp only [List.flatMap_cons]; exact (hfg _ _ hab).append (go h)
    | [], _ :: _, h | _ :: _, [], h => h.elim

end Multi

section Relation
variable (D : Dsl → List Ty → Sem) (RD : (k : Dsl) → (a : List Ty) → (D k a).1 → (D k a).1 → Prop) (R : PBij)

mutual
/-- Values of type `t` that are the same up to the renaming `R`, with bags and tables as multisets and structure
values related by `RD`. -/
def Ty.relWith : (t : Ty) → (Ty.semWith D t).1 → (Ty.semWith D t).1 → Prop
  | .int, a, b => a = b
  | .str, a, b => a = b
  | .list t, a, b => Forall2 (Ty.relWith t) a b
  | .tuple ts, a, b => Ty.relsWith ts a b
  | .fn ps r, f, g => ∀ xs ys, Ty.relsWith ps xs ys → Ty.relWith r (f xs) (g ys)
  | .adt _ _ vs, a, b => Ty.relAltsWith vs a b
  | .param _, _, _ => True
  | .bag t, a, b => Multi (Ty.relWith t) a b
  | .table k v, a, b => Multi (fun e e' => Ty.relWith k e.1 e'.1 ∧ Ty.relWith v e.2 e'.2) a.1 b.1
  | .date, a, b => a = b
  | .id, a, b => IdV.Rel R a b
  | .dsl k args, a, b => RD k args a b
def Ty.relsWith : (ts : List Ty) → (Ty.semsWith D ts).1 → (Ty.semsWith D ts).1 → Prop
  | [], _, _ => True
  | t :: ts, x, y => Ty.relWith t x.1 y.1 ∧ Ty.relsWith ts x.2 y.2
def Ty.relAltsWith : (vs : List (List Ty)) → (Ty.semAltsWith D vs).1 → (Ty.semAltsWith D vs).1 → Prop
  | [], _, _ => False
  | fs :: _, .inl x, .inl y => Ty.relsWith fs x y
  | _ :: vs, .inr x, .inr y => Ty.relAltsWith vs x y
  | _ :: _, _, _ => False
end

end Relation

/-- What structure types relate by among data: a fresh-id source is a counter, which `R` renames. -/
def Dsl.rel0 (R : PBij) : (k : Dsl) → (a : List Ty) → (Dsl.base k a).1 → (Dsl.base k a).1 → Prop
  | .fresh, _, x, y => R.rel x y
  | _, _, _, _ => True

/-- Data values related by `R`. -/
abbrev Ty.rel0 (R : PBij) (t : Ty) : t.den0 → t.den0 → Prop := Ty.relWith Dsl.base (Dsl.rel0 R) R t

section Inverse
variable {D : Dsl → List Ty → Sem} {RD RD' : (k : Dsl) → (a : List Ty) → (D k a).1 → (D k a).1 → Prop} {R : PBij}

theorem forall2_swap_iff {α β : Type} {r : α → β → Prop} {r' : β → α → Prop} (h : ∀ a b, r a b ↔ r' b a) :
    {xs : List α} → {ys : List β} → (Forall2 r xs ys ↔ Forall2 r' ys xs)
  | [], [] => Iff.rfl
  | _ :: _, _ :: _ => and_congr (h _ _) (forall2_swap_iff h)
  | [], _ :: _ | _ :: _, [] => Iff.rfl

theorem Multi.swap_iff {α β : Type} {r : α → β → Prop} {r' : β → α → Prop} (h : ∀ a b, r a b ↔ r' b a)
    {xs : List α} {ys : List β} : Multi r xs ys ↔ Multi r' ys xs :=
  ⟨fun m => m.flip.imp fun b a h' => (h a b).1 h', fun m => m.flip.imp fun a b h' => (h a b).2 h'⟩

mutual
/-- The inverse renaming relates the other way round. -/
theorem Ty.relWith_inv (hRD : ∀ k a x y, RD k a x y ↔ RD' k a y x) : (t : Ty) → (x y : (Ty.semWith D t).1) →
    (Ty.relWith D RD R t x y ↔ Ty.relWith D RD' R.inv t y x)
  | .int, _, _ | .str, _, _ | .date, _, _ => eq_comm
  | .list t, _, _ => forall2_swap_iff (Ty.relWith_inv hRD t)
  | .tuple ts, x, y => Ty.relsWith_inv hRD ts x y
  | .fn ps r, f, g => by
    show (∀ xs ys, _ → _) ↔ (∀ ys xs, _ → _)
    constructor
    · intro h ys xs hr; exact (Ty.relWith_inv hRD r _ _).1 (h xs ys ((Ty.relsWith_inv hRD ps xs ys).2 hr))
    · intro h xs ys hr; exact (Ty.relWith_inv hRD r _ _).2 (h ys xs ((Ty.relsWith_inv hRD ps xs ys).1 hr))
  | .adt _ _ vs, x, y => Ty.relAltsWith_inv hRD vs x y
  | .param _, _, _ => Iff.rfl
  | .bag t, _, _ => Multi.swap_iff (Ty.relWith_inv hRD t)
  | .table k v, _, _ => Multi.swap_iff fun _ _ => and_congr (Ty.relWith_inv hRD k _ _) (Ty.relWith_inv hRD v _ _)
  | .id, _, _ => IdV.rel_inv
  | .dsl k a, x, y => hRD k a x y
theorem Ty.relsWith_inv (hRD : ∀ k a x y, RD k a x y ↔ RD' k a y x) : (ts : List Ty) → (x y : (Ty.semsWith D ts).1) →
    (Ty.relsWith D RD R ts x y ↔ Ty.relsWith D RD' R.inv ts y x)
  | [], _, _ => Iff.rfl
  | t :: ts, x, y => and_congr (Ty.relWith_inv hRD t x.1 y.1) (Ty.relsWith_inv hRD ts x.2 y.2)
theorem Ty.relAltsWith_inv (hRD : ∀ k a x y, RD k a x y ↔ RD' k a y x) : (vs : List (List Ty)) →
    (x y : (Ty.semAltsWith D vs).1) → (Ty.relAltsWith D RD R vs x y ↔ Ty.relAltsWith D RD' R.inv vs y x)
  | [], x, _ => nomatch x
  | fs :: _, .inl x, .inl y => Ty.relsWith_inv hRD fs x y
  | _ :: vs, .inr x, .inr y => Ty.relAltsWith_inv hRD vs x y
  | _ :: _, .inl _, .inr _ | _ :: _, .inr _, .inl _ => Iff.rfl
end

end Inverse

theorem Dsl.rel0_inv {R : PBij} : ∀ k a x y, Dsl.rel0 R k a x y ↔ Dsl.rel0 R.inv k a y x
  | .fresh, _, _, _ => Iff.rfl
  | .spec, _, _, _ | .service, _, _, _ | .command, _, _, _ | .query, _, _, _ | .machine, _, _, _
  | .reaction, _, _, _ | .external, _, _, _ | .externalCommand, _, _, _ | .externalQuery, _, _, _
  | .source, _, _, _ | .declared, _, _, _ | .effect, _, _, _ | .subscription, _, _, _ | .bounds, _, _, _
  | .create, _, _, _ | .response, _, _, _ | .scenario, _, _, _ | .step, _, _, _ | .sender, _, _, _
  | .closure, _, _, _ | .effectClosure, _, _, _ => Iff.rfl

theorem Ty.rel0_inv {R : PBij} {t : Ty} {x y : t.den0} : Ty.rel0 R t x y ↔ Ty.rel0 R.inv t y x :=
  Ty.relWith_inv Dsl.rel0_inv t x y

/-! `==` on a comparable type is an equivalence: it is equality of a canonical term, which reads bags and tables in
sorted order and variants by their index. -/

section Canon
attribute [local instance] lexOrd

mutual
/-- A data value as a term that two values share exactly when `==` holds between them, on comparable types. -/
def Ty.canon : (t : Ty) → t.den0 → Erl
  | .int, n => .int n
  | .str, s => .bin s
  | .list t, xs => .list (xs.map (Ty.canon t))
  | .bag t, xs => .list (Erl.sort (xs.map (Ty.canon t)))
  | .tuple ts, x => .tuple (Ty.canons ts x)
  | .adt _ _ vs, x => Ty.canonAlts 0 vs x
  | .table k v, x =>
    let ps := Erl.sort (x.1.map fun e => (Ty.canon k e.1, Ty.canon v e.2))
    .map (ps.map (·.1)) (ps.map (·.2))
  | .date, d => .int d
  | .id, .fresh s i => .tuple [.int s, .int i]
  | .id, .named s => .bin s
  | .dsl .fresh _, n => .int (show Nat from n)
  | .param _, _ | .fn .., _ | .dsl .., _ => .atom ""
def Ty.canons : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Erl
  | [], () => []
  | t :: ts, (x, xs) => Ty.canon t x :: Ty.canons ts xs
def Ty.canonAlts (k : Nat) : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Erl
  | [], x => nomatch x
  | fs :: _, .inl x => .tuple (.int k :: Ty.canons fs x)
  | _ :: vs, .inr y => Ty.canonAlts (k + 1) vs y
end

theorem Ty.canonAlts_tag : (k : Nat) → (vs : List (List Ty)) → (y : (Ty.semAltsWith Dsl.base vs).1) →
    ∃ m ≥ k, ∃ rest, Ty.canonAlts k vs y = .tuple (.int (m : Nat) :: rest)
  | _, [], y => nomatch y
  | k, _ :: _, .inl _ => ⟨k, Nat.le_refl k, _, rfl⟩
  | k, _ :: vs, .inr y => by
    obtain ⟨m, hm, rest, h⟩ := Ty.canonAlts_tag (k + 1) vs y
    exact ⟨m, by omega, rest, h⟩

mutual
theorem Ty.canon_iff : (t : Ty) → t.comparable = true → (x y : t.den0) →
    ((Ty.semWith Dsl.base t).2 x y = true ↔ Ty.canon t x = Ty.canon t y)
  | .int, _, x, y => (beq_iff_eq (α := Int) (a := x) (b := y)).trans ⟨congrArg Erl.int, Erl.int.inj⟩
  | .str, _, x, y => (beq_iff_eq (α := String) (a := x) (b := y)).trans ⟨congrArg Erl.bin, Erl.bin.inj⟩
  | .date, _, x, y => (beq_iff_eq (α := Int) (a := x) (b := y)).trans ⟨congrArg Erl.int, Erl.int.inj⟩
  | .param _, _, x, y => by simp [Ty.semWith, Ty.canon]
  | .id, _, x, y => by cases x <;> cases y <;> simp [Ty.semWith, Ty.canon]; omega
  | .list t, h, xs, ys => by
    show listBeq _ xs ys = true ↔ Erl.list _ = Erl.list _
    rw [Erl.list.injEq]
    exact listBeq_iff (Ty.canon_iff t h) xs ys
  | .bag t, h, xs, ys => by
    show bagBeq _ xs ys = true ↔ Erl.list _ = Erl.list _
    rw [Erl.list.injEq, Erl.sort_eq_iff]
    exact bagBeq_iff (Ty.canon_iff t h) xs ys
  | .tuple ts, h, x, y => by
    show _ ↔ Erl.tuple _ = Erl.tuple _
    rw [Erl.tuple.injEq]
    exact Ty.canons_iff ts h x y
  | .adt _ _ vs, h, x, y => Ty.canonAlts_iff 0 vs h x y
  | .table k v, h, x, y => by
    simp only [Ty.comparable, Bool.and_eq_true] at h
    show tableBeq _ _ x.1 y.1 = true ↔ Erl.map _ _ = Erl.map _ _
    rw [Erl.map.injEq, map_fst_snd_iff, Erl.sort_eq_iff]
    exact tableBeq_iff (Ty.canon_iff k h.1) (Ty.canon_iff v h.2) x.2 y.2
  | .dsl k _, h, x, y => by
    cases k <;> simp [Ty.comparable] at h
    exact (beq_iff_eq (α := Nat) (a := x) (b := y)).trans
      ⟨fun e => congrArg (fun n : Nat => Erl.int n) e, fun e => Int.ofNat_inj.1 (Erl.int.inj e)⟩
  | .fn .., h, _, _ => by simp [Ty.comparable] at h
theorem Ty.canons_iff : (ts : List Ty) → Ty.comparables ts = true → (x y : (Ty.semsWith Dsl.base ts).1) →
    ((Ty.semsWith Dsl.base ts).2 x y = true ↔ Ty.canons ts x = Ty.canons ts y)
  | [], _, (), () => by simp [Ty.semsWith, Ty.canons]
  | t :: ts, h, (x, xs), (y, ys) => by
    simp only [Ty.comparables, Bool.and_eq_true] at h
    show ((Ty.semWith Dsl.base t).2 x y && (Ty.semsWith Dsl.base ts).2 xs ys) = true ↔ _
    simp only [Bool.and_eq_true, Ty.canons, List.cons.injEq, Ty.canon_iff t h.1 x y, Ty.canons_iff ts h.2 xs ys]
theorem Ty.canonAlts_iff : (k : Nat) → (vs : List (List Ty)) → Ty.comparabless vs = true →
    (x y : (Ty.semAltsWith Dsl.base vs).1) →
    ((Ty.semAltsWith Dsl.base vs).2 x y = true ↔ Ty.canonAlts k vs x = Ty.canonAlts k vs y)
  | _, [], _, x, _ => nomatch x
  | k, fs :: _, h, .inl x, .inl y => by
    simp only [Ty.comparabless, Bool.and_eq_true] at h
    show (Ty.semsWith Dsl.base fs).2 x y = true ↔ _
    simp only [Ty.canonAlts, Erl.tuple.injEq, List.cons.injEq, true_and]
    exact Ty.canons_iff fs h.1 x y
  | k, _ :: vs, h, .inr x, .inr y => by
    simp only [Ty.comparabless, Bool.and_eq_true] at h
    simp only [Ty.semAltsWith, Sem.sum, Ty.canonAlts]
    exact Ty.canonAlts_iff (k + 1) vs h.2 x y
  | k, _ :: vs, _, .inl x, .inr y => by
    simp only [Ty.semAltsWith, Sem.sum, Bool.false_eq_true, false_iff]
    obtain ⟨m, hm, rest, ht⟩ := Ty.canonAlts_tag (k + 1) vs y
    simp only [Ty.canonAlts, ht, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj]
    omega
  | k, _ :: vs, _, .inr x, .inl y => by
    simp only [Ty.semAltsWith, Sem.sum, Bool.false_eq_true, false_iff]
    obtain ⟨m, hm, rest, ht⟩ := Ty.canonAlts_tag (k + 1) vs x
    simp only [Ty.canonAlts, ht, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj]
    omega
end

end Canon

/-- Gleam's `==` on data, as data values carry it. -/
abbrev Ty.deq0 (t : Ty) : t.den0 → t.den0 → Bool := (Ty.semWith Dsl.base t).2

theorem Ty.deq0_symm {t : Ty} (h : t.comparable = true) {x y : t.den0} (e : t.deq0 x y = true) : t.deq0 y x = true :=
  (Ty.canon_iff t h y x).2 ((Ty.canon_iff t h x y).1 e).symm

theorem Ty.deq0_trans {t : Ty} (h : t.comparable = true) {x y z : t.den0} (e : t.deq0 x y = true)
    (e' : t.deq0 y z = true) : t.deq0 x z = true :=
  (Ty.canon_iff t h x z).2 (((Ty.canon_iff t h x y).1 e).trans ((Ty.canon_iff t h y z).1 e'))

/-! Related values compare alike: `==` reads neither the names a renaming changes nor the order of a bag or table. -/

section Deq
variable {α β κ κ' ν ν' : Type}

theorem listBeq_forall2 {r : α → β → Prop} {f : α → α → Bool} {g : β → β → Bool}
    (hfg : ∀ a b a' b', r a b → r a' b' → f a a' = g b b') :
    {xs : List α} → {ys : List β} → {xs' : List α} → {ys' : List β} → Forall2 r xs ys → Forall2 r xs' ys' →
    listBeq f xs xs' = listBeq g ys ys'
  | [], [], [], [], _, _ | [], [], _ :: _, _ :: _, _, _ | _ :: _, _ :: _, [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, ⟨h1, h⟩, ⟨h1', h'⟩ => by
    simp only [listBeq, hfg _ _ _ _ h1 h1', listBeq_forall2 hfg h h']
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim
  | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h => h.elim

theorem countBy_forall2 {r : α → β → Prop} {f : α → α → Bool} {g : β → β → Bool}
    (hfg : ∀ a b a' b', r a b → r a' b' → f a a' = g b b') {x : α} {y : β} (hxy : r x y) {xs : List α} {ys : List β}
    (h : Forall2 r xs ys) : countBy f x xs = countBy g y ys :=
  forall2_length (forall2_filter (fun _ _ hab => hfg _ _ _ _ hxy hab) h)

theorem bagBeq_forall2 {r : α → β → Prop} {f : α → α → Bool} {g : β → β → Bool}
    (hfg : ∀ a b a' b', r a b → r a' b' → f a a' = g b b') {xs : List α} {ys : List β} {xs' : List α}
    {ys' : List β} (h : Forall2 r xs ys) (h' : Forall2 r xs' ys') : bagBeq f xs xs' = bagBeq g ys ys' := by
  simp only [bagBeq, forall2_length h, forall2_length h']
  congr 1
  exact forall2_all_eq (fun x y hxy => by
    rw [countBy_forall2 hfg hxy h, countBy_forall2 hfg hxy h']) h

theorem bagBeq_multi {r : α → β → Prop} {f : α → α → Bool} {g : β → β → Bool}
    (hfg : ∀ a b a' b', r a b → r a' b' → f a a' = g b b') {xs : List α} {ys : List β} {xs' : List α}
    {ys' : List β} : Multi r xs ys → Multi r xs' ys' → bagBeq f xs xs' = bagBeq g ys ys'
  | ⟨_, h, hz⟩, ⟨_, h', hz'⟩ => (bagBeq_forall2 hfg h h').trans (bagBeq_perm g hz hz')

theorem lookupBy_forall2 {rk : κ → κ' → Prop} {rv : ν → ν' → Prop} {fk : κ → κ → Bool} {gk : κ' → κ' → Bool}
    (hk : ∀ a b a' b', rk a b → rk a' b' → fk a a' = gk b b') {k : κ} {k' : κ'} (hkk : rk k k') :
    {l : List (κ × ν)} → {l' : List (κ' × ν')} → Forall2 (fun e e' => rk e.1 e'.1 ∧ rv e.2 e'.2) l l' →
    Option.Rel rv (lookupBy fk k l) (lookupBy gk k' l')
  | [], [], _ => .none
  | (a, v) :: _, (b, w) :: _, ⟨⟨ha, hv⟩, h⟩ => by
    simp only [lookupBy, hk _ _ _ _ hkk ha]
    split
    · exact .some hv
    · exact lookupBy_forall2 hk hkk h
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem lookupBy_eq_find {fk : κ → κ → Bool} {k : κ} :
    (l : List (κ × ν)) → lookupBy fk k l = (l.find? fun e => fk k e.1).map (·.2)
  | [] => rfl
  | (a, v) :: l => by
    simp only [lookupBy, List.find?_cons]
    split <;> simp_all [lookupBy_eq_find l]

theorem pairwise_eq_of {α : Type} {P : α → α → Prop} :
    {l : List α} → l.Pairwise P → ∀ {a b}, a ∈ l → b ∈ l → ¬P a b → ¬P b a → a = b
  | [], _, _, _, ha, _, _, _ => nomatch ha
  | _ :: _, h, _, _, ha, hb, hab, hba => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ea | ta <;> rcases List.mem_cons.1 hb with eb | tb
    · rw [ea, eb]
    · subst ea; exact absurd (h.1 _ tb) hab
    · subst eb; exact absurd (h.1 _ ta) hba
    · exact pairwise_eq_of h.2 ta tb hab hba

/-- Under an equivalence on keys, a lookup in a table with unique keys reads no order. -/
theorem lookupBy_perm {fk : κ → κ → Bool} (hsym : ∀ a b, fk a b = true → fk b a = true)
    (htr : ∀ a b c, fk a b = true → fk b c = true → fk a c = true) {l l' : List (κ × ν)} (hu : KeysUnique fk l)
    (hp : l.Perm l') (k : κ) : lookupBy fk k l = lookupBy fk k l' := by
  rw [lookupBy_eq_find, lookupBy_eq_find, find?_perm_unique hp]
  intro a ha b hb hka hkb
  have hab : fk a.1 b.1 = true := htr _ _ _ (hsym _ _ hka) hkb
  exact pairwise_eq_of hu ha hb (fun h => by rw [h.1] at hab; cases hab)
    (fun h => by rw [h.2] at hab; cases hab)

theorem keysUnique_perm {fk : κ → κ → Bool} {l l' : List (κ × ν)} (hp : l.Perm l') (hu : KeysUnique fk l) :
    KeysUnique fk l' :=
  hu.perm hp fun h => ⟨h.2, h.1⟩

theorem tableBeq_forall2 {rk : κ → κ' → Prop} {rv : ν → ν' → Prop} {fk : κ → κ → Bool} {gk : κ' → κ' → Bool}
    {fv : ν → ν → Bool} {gv : ν' → ν' → Bool} (hk : ∀ a b a' b', rk a b → rk a' b' → fk a a' = gk b b')
    (hv : ∀ a b a' b', rv a b → rv a' b' → fv a a' = gv b b') {xs ys : List (κ × ν)} {xs' ys' : List (κ' × ν')}
    (h : Forall2 (fun e e' => rk e.1 e'.1 ∧ rv e.2 e'.2) xs xs')
    (h' : Forall2 (fun e e' => rk e.1 e'.1 ∧ rv e.2 e'.2) ys ys') : tableBeq fk fv xs ys = tableBeq gk gv xs' ys' := by
  simp only [tableBeq, forall2_length h, forall2_length h']
  congr 1
  refine forall2_all_eq (fun ⟨a, v⟩ ⟨b, w⟩ ⟨hab, hvw⟩ => ?_) h
  have := lookupBy_forall2 (rv := rv) hk hab h'
  revert this
  cases lookupBy fk a ys <;> cases lookupBy gk b ys' <;> intro hr <;> cases hr
  · rfl
  · exact hv _ _ _ _ hvw (by assumption)

theorem tableBeq_perm {fk : κ → κ → Bool} (fv : ν → ν → Bool) (hsym : ∀ a b, fk a b = true → fk b a = true)
    (htr : ∀ a b c, fk a b = true → fk b c = true → fk a c = true) {xs xs' ys ys' : List (κ × ν)} (hx : xs.Perm xs')
    (hy : ys.Perm ys') (hu : KeysUnique fk ys) : tableBeq fk fv xs ys = tableBeq fk fv xs' ys' := by
  simp only [tableBeq, hx.length_eq, hy.length_eq, lookupBy_perm hsym htr hu hy, hx.all_eq]

end Deq

mutual
/-- `==` on related values of a comparable type gives the same answer. -/
theorem Ty.rel0_deq {R : PBij} : (t : Ty) → t.comparable = true → {x y x' y' : t.den0} → Ty.rel0 R t x y →
    Ty.rel0 R t x' y' → t.deq0 x x' = t.deq0 y y'
  | .int, _, _, _, _, _, h, h' | .str, _, _, _, _, _, h, h' | .date, _, _, _, _, _, h, h' => by
    show (_ == _) = (_ == _)
    rw [show _ = _ from h, show _ = _ from h']
  | .param _, _, _, _, _, _, _, _ => rfl
  | .id, _, _, _, _, _, h, h' => decide_eq_decide.2 (IdV.rel_eq h h')
  | .list t, hc, x, y, x', y', h, h' =>
    show listBeq (Ty.deq0 t) x x' = listBeq (Ty.deq0 t) y y' from
    listBeq_forall2 (r := Ty.rel0 R t) (fun _ _ _ _ => Ty.rel0_deq t hc) h h'
  | .bag t, hc, x, y, x', y', h, h' =>
    show bagBeq (Ty.deq0 t) x x' = bagBeq (Ty.deq0 t) y y' from
    bagBeq_multi (r := Ty.rel0 R t) (fun _ _ _ _ => Ty.rel0_deq t hc) h h'
  | .tuple ts, hc, _, _, _, _, h, h' => Ty.rels0_deq ts hc h h'
  | .adt _ _ vs, hc, _, _, _, _, h, h' => Ty.relAlts0_deq vs hc h h'
  | .table k v, hc, x, y, x', y', ⟨zs, h, hz⟩, ⟨zs', h', hz'⟩ => by
    simp only [Ty.comparable, Bool.and_eq_true] at hc
    show tableBeq (Ty.deq0 k) (Ty.deq0 v) x.1 x'.1 = tableBeq (Ty.deq0 k) (Ty.deq0 v) y.1 y'.1
    rw [tableBeq_forall2 (fk := Ty.deq0 k) (gk := Ty.deq0 k) (fv := Ty.deq0 v) (gv := Ty.deq0 v)
      (fun _ _ _ _ => Ty.rel0_deq k hc.1) (fun _ _ _ _ => Ty.rel0_deq v hc.2) h h']
    exact tableBeq_perm (fk := Ty.deq0 k) _ (fun _ _ => Ty.deq0_symm hc.1) (fun _ _ _ => Ty.deq0_trans hc.1) hz hz'
      (keysUnique_perm hz'.symm y'.2)
  | .dsl k _, hc, x, y, x', y', h, h' => by
    cases k <;> simp [Ty.comparable] at hc
    revert x y x' y'
    show ∀ x y x' y' : Nat, R.rel x y → R.rel x' y' → (x == x') = (y == y')
    intro x y x' y' h h'
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun e => R.func h (e ▸ h'), fun e => R.inj h (e ▸ h')⟩
  | .fn .., hc, _, _, _, _, _, _ => by simp [Ty.comparable] at hc
theorem Ty.rels0_deq {R : PBij} : (ts : List Ty) → Ty.comparables ts = true → {x y x' y' : (Ty.semsWith Dsl.base ts).1} →
    Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x y → Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x' y' →
    (Ty.semsWith Dsl.base ts).2 x x' = (Ty.semsWith Dsl.base ts).2 y y'
  | [], _, _, _, _, _, _, _ => rfl
  | t :: ts, hc, _, _, _, _, ⟨h1, h⟩, ⟨h1', h'⟩ => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    show (Ty.deq0 t _ _ && _) = (Ty.deq0 t _ _ && _)
    rw [Ty.rel0_deq t hc.1 h1 h1', Ty.rels0_deq ts hc.2 h h']
theorem Ty.relAlts0_deq {R : PBij} : (vs : List (List Ty)) → Ty.comparabless vs = true →
    {x y x' y' : (Ty.semAltsWith Dsl.base vs).1} →
    Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x y → Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x' y' →
    (Ty.semAltsWith Dsl.base vs).2 x x' = (Ty.semAltsWith Dsl.base vs).2 y y'
  | [], _, x, _, _, _, _, _ => nomatch x
  | fs :: _, hc, .inl _, .inl _, .inl _, .inl _, h, h' => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    exact Ty.rels0_deq fs hc.1 h h'
  | _ :: vs, hc, .inr _, .inr _, .inr _, .inr _, h, h' => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    exact Ty.relAlts0_deq vs hc.2 h h'
  | _ :: _, _, .inl _, .inl _, .inr _, .inr _, _, _ | _ :: _, _, .inr _, .inr _, .inl _, .inl _, _, _ => rfl
  | _ :: _, _, .inl _, .inr _, _, _, h, _ | _ :: _, _, .inr _, .inl _, _, _, h, _ => h.elim
  | _ :: _, _, _, _, .inl _, .inr _, _, h | _ :: _, _, _, _, .inr _, .inl _, _, h => h.elim
end

/-! Structure values. A kept function relates by its meaning; an effect, a request and a sender relate when they name
the same thing with the same types and their values and kept functions relate. These are the values a step keeps
between internal steps. -/

/-- Kept functions whose meanings relate. -/
def Fun.Rel (R : PBij) {t : Ty} (f g : Fun t) : Prop := Ty.rel0 R t f.fn g.fn

inductive WireVal.Rel (R : PBij) : WireVal → WireVal → Prop
  | mk {t : Ty} {x y : t.den0} : Ty.rel0 R t x y → WireVal.Rel R ⟨t, x⟩ ⟨t, y⟩

inductive Sender.Rel (R : PBij) : Sender → Sender → Prop
  | machine (name : String) {k k' : WireVal} : WireVal.Rel R k k' → Sender.Rel R (.machine name k) (.machine name k')
  | reaction (name : String) : Sender.Rel R (.reaction name) (.reaction name)

inductive RequestV.Rel (R : PBij) {e : Ty} : RequestV e → RequestV e → Prop
  | mk (name : String) (input output : Ty) (rejection : Option Ty) {value value' : input.den0}
      {holds holds' : Option (Fun (Ty.fn [input, answerTy output rejection] Ty.rules))}
      {onAnswer onAnswer' : Fun (Ty.fn [answerTy output rejection] (.list e))} :
      Ty.rel0 R input value value' → Option.Rel (Fun.Rel R) holds holds' → Fun.Rel R onAnswer onAnswer' →
      RequestV.Rel R ⟨name, input, output, rejection, value, holds, onAnswer⟩
        ⟨name, input, output, rejection, value', holds', onAnswer'⟩

inductive EffectV.Rel (R : PBij) {e : Ty} : EffectV e → EffectV e → Prop
  | request {x y : RequestV e} : RequestV.Rel R x y → EffectV.Rel R (.request x) (.request y)
  | command (name : String) (c input rejection : Ty) {caller caller' : c.den0} {value value' : input.den0}
      {onAnswer onAnswer' : Fun (Ty.fn [Ty.result Ty.nil rejection] (.list e))} :
      Ty.rel0 R c caller caller' → Ty.rel0 R input value value' → Fun.Rel R onAnswer onAnswer' →
      EffectV.Rel R (.command name c input rejection caller value onAnswer)
        (.command name c input rejection caller' value' onAnswer')
  | query (name : String) (c input output : Ty) {caller caller' : c.den0} {value value' : input.den0}
      {onAnswer onAnswer' : Fun (Ty.fn [output] (.list e))} :
      Ty.rel0 R c caller caller' → Ty.rel0 R input value value' → Fun.Rel R onAnswer onAnswer' →
      EffectV.Rel R (.query name c input output caller value onAnswer) (.query name c input output caller' value' onAnswer')

/-! What a spec's structure values keep, each related to itself by `R`: the functions a step runs and the values a step
reads. A service whose parts are so for every `R` respects every renaming (`Step.ServiceV.Equivariant`). -/

section Self
variable (R : PBij) {r e c : Ty}

structure CommandV.Self (x : CommandV r e c) : Prop where
  callers : Ty.rel0 R (.list c) x.callers x.callers
  accepts : Fun.Rel R x.accepts x.accepts
  decide : Fun.Rel R x.decide x.decide
  ensures : Fun.Rel R x.ensures x.ensures

structure QueryV.Self (x : QueryV r c) : Prop where
  callers : Ty.rel0 R (.list c) x.callers x.callers
  accepts : Fun.Rel R x.accepts x.accepts
  resolve : Fun.Rel R x.resolve x.resolve

/-- A machine's functions, its initial state, and the values its effect function captured. -/
structure MachineV.Self (m : MachineV r e) : Prop where
  instances : Fun.Rel R m.instances m.instances
  on : Fun.Rel R m.on m.on
  after : Fun.Rel R m.after m.after
  initial : Ty.rel0 R m.state m.initial m.initial
  effect : Ty.rel0 R (.tuple m.effect.Γ) m.effect.env m.effect.env

/-- The values a reaction's function captured. -/
def ReactionV.Self (x : ReactionV r e) : Prop := Ty.rel0 R (.tuple x.react.Γ) x.react.env x.react.env

def DeclaredV.Self : DeclaredV → Prop
  | .command _ _ _ x => x.Self R
  | .query _ _ x => x.Self R
  | _ => True

structure ServiceV.Self (v : ServiceV) : Prop where
  init : Ty.rel0 R v.records v.init v.init
  apply : Fun.Rel R v.apply v.apply
  subscribes : ∀ s ∈ v.subscribes, Fun.Rel R s.wrap s.wrap
  commands : ∀ x ∈ v.commands, x.Self R
  queries : ∀ x ∈ v.queries, x.Self R
  machines : ∀ m ∈ v.machines, m.Self R
  reactions : ∀ x ∈ v.reactions, x.Self R

end Self

/-- A subscription without the source `spec` finds for it. -/
def SubscriptionV.stripped {e : Ty} (s : SubscriptionV e) : SubscriptionV e := { s with source := "" }

/-- A service without what `spec` fills in, which `ServiceV.Self` does not read. -/
def ServiceV.stripped (v : ServiceV) : ServiceV :=
  { v with declared := [], subscribes := v.subscribes.map SubscriptionV.stripped }

/-- What structure values relate by. A command, query, machine or reaction is read by a step through its name, so
related ones have the same name; a structure value that is the same on both sides keeps parts related to themselves,
which is all a closed program's spec gives, since evaluating it relates it to itself. A service relates once `spec`'s
additions are set aside, since `spec` writes them from the other services. The other values a spec is built from hold
no name a step makes, so they relate trivially. -/
def Dsl.relV (R : PBij) : (k : Dsl) → (a : List Ty) → (Dsl.val k a).1 → (Dsl.val k a).1 → Prop
  | .fresh, _, x, y => R.rel x y
  | .effect, [_], x, y => EffectV.Rel R x y
  | .closure, [_], f, g => Fun.Rel R f g
  | .effectClosure, [.fn _ _], f, g => f = g → Ty.rel0 R (.tuple f.Γ) f.env f.env
  | .sender, _, x, y => Sender.Rel R x y
  | .subscription, [_], x, y => x.stripped = y.stripped → Fun.Rel R x.wrap x.wrap
  | .spec, _, s, s' => s = s' → ∀ v ∈ (s : SpecV).services, v.Self R
  | .service, _, v, w => ServiceV.stripped v = ServiceV.stripped w → ServiceV.Self R v
  | .declared, _, d, d' => d = d' → DeclaredV.Self R d
  | .command, [_, _, _, _, _], x, y => x.1.name = y.1.name ∧ (x = y → x.1.Self R)
  | .query, [_, _, _, _], x, y => x.1.name = y.1.name ∧ (x = y → x.1.Self R)
  | .machine, [_, _], x, y => x.name = y.name ∧ (x = y → x.Self R)
  | .reaction, [_, _], x, y => x.name = y.name ∧ (x = y → ReactionV.Self R x)
  | .externalCommand, [_, _, _], x, y => x = y
  | .externalQuery, [_, _], x, y => x.1 = y.1 ∧ Fun.Rel R x.2 y.2
  | .source, [_], x, y => x = y
  | _, _, _, _ => True

/-- Values related by `R`, at the level expressions evaluate at. -/
abbrev Ty.relV (R : PBij) (t : Ty) : t.den → t.den → Prop := Ty.relWith Dsl.val (Dsl.relV R) R t

section Up
variable {α β : Type} {r : α → α → Prop}

theorem forall2_map_iff {f : β → α} : {xs ys : List β} → (Forall2 r (xs.map f) (ys.map f) ↔ Forall2 (fun a b => r (f a) (f b)) xs ys)
  | [], [] => Iff.rfl
  | _ :: _, _ :: _ => and_congr Iff.rfl forall2_map_iff
  | [], _ :: _ | _ :: _, [] => Iff.rfl

theorem Multi.map_iff {f : β → α} {g : α → β} (hgf : ∀ a, f (g a) = a) (hfg : ∀ b, g (f b) = b) {xs ys : List β} :
    Multi r (xs.map f) (ys.map f) ↔ Multi (fun a b => r (f a) (f b)) xs ys := by
  constructor
  · rintro ⟨zs, h, hz⟩
    have ez : zs = (zs.map g).map f := by simp [Function.comp_def, hgf]
    refine ⟨zs.map g, ?_, ?_⟩
    · rw [ez, forall2_map_iff] at h; exact h
    · have := hz.map g
      simpa [Function.comp_def, hfg] using this
  · rintro ⟨zs, h, hz⟩
    exact ⟨zs.map f, forall2_map_iff.2 h, hz.map f⟩

end Up

theorem forall2_congr {α β : Type} {r r' : α → β → Prop} (h : ∀ a b, r a b ↔ r' a b) :
    {xs : List α} → {ys : List β} → (Forall2 r xs ys ↔ Forall2 r' xs ys)
  | [], [] => Iff.rfl
  | _ :: _, _ :: _ => and_congr (h _ _) (forall2_congr h)
  | [], _ :: _ | _ :: _, [] => Iff.rfl

theorem Multi.congr {α β : Type} {r r' : α → β → Prop} (h : ∀ a b, r a b ↔ r' a b) {xs : List α} {ys : List β} :
    Multi r xs ys ↔ Multi r' xs ys :=
  ⟨Multi.imp fun a b => (h a b).1, Multi.imp fun a b => (h a b).2⟩

mutual
/-- Data relates alike at both levels. -/
theorem Ty.relV_up {R : PBij} : (t : Ty) → (h : t.isData = true) → (x y : t.den0) →
    (Ty.relV R t (Ty.up t h x) (Ty.up t h y) ↔ Ty.rel0 R t x y)
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ | .id, _, _, _ | .param _, _, _, _ => Iff.rfl
  | .list t, h, xs, ys => by
    have ht : t.isData = true := h
    rw [Ty.up_list t h ht, Ty.up_list t h ht]
    exact forall2_map_iff.trans (forall2_congr (Ty.relV_up t ht))
  | .bag t, h, xs, ys => by
    have ht : t.isData = true := h
    rw [Ty.up_bag t h ht, Ty.up_bag t h ht]
    exact (Multi.map_iff (Ty.up_down t ht) (Ty.down_up t ht)).trans (Multi.congr (Ty.relV_up t ht))
  | .table k v, h, x, y => by
    have hk : k.isData = true := (Bool.and_eq_true _ _ ▸ h).1
    have hv : v.isData = true := (Bool.and_eq_true _ _ ▸ h).2
    show Multi _ (Ty.up _ h x).1 (Ty.up _ h y).1 ↔ Multi _ x.1 y.1
    rw [Ty.up_table k v h hk hv, Ty.up_table k v h hk hv]
    refine (Multi.map_iff (g := fun p => (Ty.down k hk p.1, Ty.down v hv p.2))
      (fun p => by simp [Ty.up_down]) (fun p => by simp [Ty.down_up])).trans (Multi.congr fun _ _ => ?_)
    exact and_congr (Ty.relV_up k hk _ _) (Ty.relV_up v hv _ _)
  | .tuple ts, h, x, y => Ty.relsV_up ts h x y
  | .adt k a vs, h, x, y => Ty.relAltsV_up k a vs h x y
  | .fn ps r, h, f, g => by
    have hps : (Ty.tuple ps).isData = true := (Bool.and_eq_true _ _ ▸ h).1
    have hr : r.isData = true := (Bool.and_eq_true _ _ ▸ h).2
    show (∀ xs ys, _ → _) ↔ (∀ xs ys, _ → _)
    constructor
    · intro H xs ys hxy
      have := H (Ty.up _ hps xs) (Ty.up _ hps ys) ((Ty.relsV_up ps hps xs ys).2 hxy)
      erw [Ty.up_fn ps r h hps hr, Ty.up_fn ps r h hps hr] at this
      exact (Ty.relV_up r hr _ _).1 this
    · intro H xs ys hxy
      rw [← Ty.up_down _ hps xs, ← Ty.up_down _ hps ys] at hxy ⊢
      erw [Ty.up_fn ps r h hps hr, Ty.up_fn ps r h hps hr]
      exact (Ty.relV_up r hr _ _).2 (H _ _ ((Ty.relsV_up ps hps _ _).1 hxy))
  | .dsl k _, h, _, _ => by cases k <;> simp [Ty.isData] at h; exact Iff.rfl
theorem Ty.relsV_up {R : PBij} : (ts : List Ty) → (h : (Ty.tuple ts).isData = true) → (x y : (Ty.tuple ts).den0) →
    (Ty.relsWith Dsl.val (Dsl.relV R) R ts (Ty.up (.tuple ts) h x) (Ty.up (.tuple ts) h y) ↔
      Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x y)
  | [], _, _, _ => Iff.rfl
  | t :: ts, h, x, y => by
    have ht : t.isData = true := (Bool.and_eq_true _ _ ▸ h).1
    have hts : (Ty.tuple ts).isData = true := (Bool.and_eq_true _ _ ▸ h).2
    rw [Ty.up_tuple t ts h ht hts x, Ty.up_tuple t ts h ht hts y]
    exact and_congr (Ty.relV_up t ht x.1 y.1) (Ty.relsV_up ts hts x.2 y.2)
theorem Ty.relAltsV_up {R : PBij} (k : Nat) (a : List Ty) : (vs : List (List Ty)) →
    (h : (Ty.adt k a vs).isData = true) → (x y : (Ty.adt k a vs).den0) →
    (Ty.relAltsWith Dsl.val (Dsl.relV R) R vs (Ty.up _ h x) (Ty.up _ h y) ↔
      Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x y)
  | [], _, x, _ => nomatch x
  | fs :: vs, h, .inl x, .inl y => by
    have hfs : (Ty.tuple fs).isData = true := (Bool.and_eq_true _ _ ▸ h).1
    rw [Ty.up_inl k a fs vs h hfs x, Ty.up_inl k a fs vs h hfs y]
    exact Ty.relsV_up fs hfs x y
  | fs :: vs, h, .inr x, .inr y => by
    have hvs : (Ty.adt k a vs).isData = true := (Bool.and_eq_true _ _ ▸ h).2
    rw [Ty.up_inr k a fs vs h hvs x, Ty.up_inr k a fs vs h hvs y]
    exact Ty.relAltsV_up k a vs hvs x y
  | fs :: vs, h, .inl x, .inr y => by
    rw [Ty.up_inl k a fs vs h (Bool.and_eq_true _ _ ▸ h).1 x, Ty.up_inr k a fs vs h (Bool.and_eq_true _ _ ▸ h).2 y]
    exact Iff.rfl
  | fs :: vs, h, .inr x, .inl y => by
    rw [Ty.up_inr k a fs vs h (Bool.and_eq_true _ _ ▸ h).2 x, Ty.up_inl k a fs vs h (Bool.and_eq_true _ _ ▸ h).1 y]
    exact Iff.rfl
end

end Tazuna.Ir
