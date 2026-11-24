import Tazuna.Smt.Kept
import Tazuna.Smt.Fits

/-! A code's condition is exact: it is false only where the evaluation really outgrows a slot count (`Expr.fits` with
the layout's counts), and true otherwise. T1 (`encode_agrees`) takes the condition as a hypothesis, so a condition
stronger than this would make T1 hold vacuously for evaluations within the bounds and a script unsat for a real
step. `encode_exact` rules that out. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The slot count the layout gives a type. -/
def Layout.count (L : Layout) (t : Ty) : Nat :=
  match L.find? t with
  | some (_, n) => n
  | none => 0

section
variable {M : Model} {L : Layout}

theorem occupied_length_le : (sv : List (Bool × List Val)) → (occupied sv).length ≤ sv.length
  | [] => by simp [occupied]
  | (b, vs) :: sv => by
    have := occupied_length_le sv
    cases b <;> simp [occupied] at this ⊢ <;> omega

theorem occupied_lt_iff : (sv : List (Bool × List Val)) → ((occupied sv).length < sv.length ↔ sv.all (·.1) = false)
  | [] => by simp [occupied]
  | (b, vs) :: sv => by
    have ih := occupied_lt_iff sv
    have := occupied_length_le sv
    cases b <;> (simp [occupied] at ih this ⊢; try omega)

/-- Inserting into slots finds a free one exactly when fewer slots are occupied than there are. -/
theorem insert_exact {x : List Term} {S : List Slot} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv)
    (hw : ∀ q ∈ sv, q.2.length = x.length) {p : Term} (hp : p.denote M = .bool true) :
    Holds M (.not (insertSlots x p S).2) ↔ (occupied sv).length < sv.length := by
  obtain ⟨-, h2⟩ := insertSlots_den x _ rfl p true hp hS hw
  obtain ⟨-, h3⟩ := insertVals_occupied (Term.denotes M x) true sv
  rw [occupied_lt_iff]
  simp [Holds, Term.denote, h2, h3, Val.toBool]

/-- Moving the occupied slots of `S` into `T` finds a slot for each exactly when all of them fit. -/
theorem moveAll_exact (d dt w : Nat) : {S : List Slot} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    (∀ p ∈ sv, p.2.length = w) → {T : List Slot} → {tv : List (Bool × List Val)} → SlotsDen M T tv →
    (∀ p ∈ tv, p.2.length = w) →
    (Holds M (moveAll d dt w T S).2 ↔ (occupied sv).length + (occupied tv).length ≤ tv.length)
  | [], [], _, _, T, tv, _, _ => by
    simp only [moveAll, occupied, List.filterMap_nil, List.length_nil, Nat.zero_add]
    exact ⟨fun _ => occupied_length_le tv, fun _ => holds_tt⟩
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hx, hS⟩, hw, T, tv, hT, htw => by
    simp only [moveAll]
    have hvs : vs.length = w := hw (b, vs) (by simp)
    have hxl : xs.length = w := by rw [← hvs, ← hx, denotes_eq_map, List.length_map]
    have hw' : ∀ p ∈ sv, p.2.length = w := fun q hq => hw q (by simp [hq])
    obtain ⟨h1, h2⟩ := insertSlots_den xs vs hx f b hf hT (fun q hq => by rw [htw q hq, hxl])
    obtain ⟨hl1, hw1⟩ := insertVals_length vs w hvs b tv htw
    have hT1 := slotsOf_den d dt w _ _ (slotsTerm_den d dt h1) hw1
    rw [← slotsDen_length h1] at hT1
    have ih := moveAll_exact d dt w hS hw' hT1 hw1
    rw [holds_and, ih, hl1]
    obtain ⟨hocc, hp⟩ := insertVals_occupied vs b tv
    have hle := occupied_length_le tv
    cases b with
    | false =>
      simp only [insertVals_false] at hocc ⊢
      simp [Holds, Term.denote, h2, insertVals_false, Val.toBool, occupied]
    | true =>
      have hnot : Holds M (.not (insertSlots xs f T).2) ↔ (occupied tv).length < tv.length := by
        rw [occupied_lt_iff]
        simp only [Holds, Term.denote, h2, hp, Val.toBool, Bool.true_and]
        cases tv.all (·.1) <;> simp
      have hc : (occupied ((true, vs) :: sv)).length = (occupied sv).length + 1 := by simp [occupied]
      rw [hnot, hc]
      have hfit : ∀ (hlt : (occupied tv).length < tv.length),
          (occupied (insertVals vs true tv).1).length = (occupied tv).length + 1 := by
        intro hlt
        have hp' : (insertVals vs true tv).2 = false := by
          rw [hp]; simpa using (occupied_lt_iff tv).1 hlt
        rw [hp'] at hocc
        simp only [and_self, ite_true, List.singleton_append] at hocc
        rw [hocc.length_eq]; rfl
      constructor
      · rintro ⟨hlt, h⟩
        rw [hfit hlt] at h; omega
      · intro h
        have hlt : (occupied tv).length < tv.length := by omega
        exact ⟨hlt, by rw [hfit hlt]; omega⟩
  | [], _ :: _, h, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _ => h.elim

/-- Carrying slots into `n` slots succeeds exactly when the occupied ones fit. -/
theorem resize_exact (d dt n : Nat) (dflt : List Term) {S : List Slot} {sv : List (Bool × List Val)}
    (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = dflt.length) :
    Holds M (resizeSlots d dt dflt n S).2 ↔ (occupied sv).length ≤ n := by
  by_cases hle : S.length ≤ n
  · simp only [resizeSlots, hle, ↓reduceIte]
    have := occupied_length_le sv
    rw [← slotsDen_length hS] at this
    exact ⟨fun _ => by omega, fun _ => holds_tt⟩
  · simp only [resizeSlots, hle, ↓reduceIte]
    have hfree : ∀ p ∈ List.replicate n (false, Term.denotes M dflt), p.2.length = dflt.length := by
      intro p hp
      simp only [List.mem_replicate] at hp
      rw [hp.2, denotes_eq_map, List.length_map]
    rw [moveAll_exact d dt dflt.length hS hw (empty_den dflt n) hfree, occupied_empty]
    simp

theorem collD_count {c : Ty} {item : List Ty} {d n dt : Nat} (h : collD L c item = .ok (d, n, dt)) : L.count c = n := by
  obtain ⟨hf, -⟩ := collD_ok h
  simp [Layout.count, hf]

/-- A collection built from slots: its condition holds exactly when the occupied ones fit its type's count. -/
theorem collOf_exact {c : Ty} {item : List Ty} {S : List Slot} {sv : List (Bool × List Val)} {r cond : Term}
    (h : collOf L c item S = .ok (r, cond)) (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = item.length) :
    Holds M cond ↔ (occupied sv).length ≤ L.count c := by
  simp only [collOf] at h
  obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨dflt, h2, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hl := mapM_some_length _ item dflt (need_ok.1 h2)
  rw [collD_count h1]
  exact resize_exact d dt n dflt hS (hl ▸ hw)

/-- The guards of per-slot conditions hold exactly when the property each slot's condition decides holds of every
item. -/
theorem guards_exact {α : Type} {E : α → List Val → Prop} {P : α → Prop} (G : Slot → Term × Term → Prop)
    (hG : ∀ sl r y, G sl r → E y (Term.denotes M sl.2) → (Holds M r.2 ↔ P y)) :
    {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List α} → {R : List (Term × Term)} →
    SlotsDen M S sv → Holds2 E ys sv → Forall2 G S R →
    (Holds M (guardsT S (R.map (·.2))) ↔ ∀ y ∈ ys, P y)
  | [], [], [], [], _, _, _ => by simp [guardsT, allT, Holds, tt, Term.denote, Val.toBool]
  | [], [], _ :: _, [], _, h, _ => nomatch h
  | (f, xs) :: S, (false, vs) :: sv, ys, r :: R, ⟨hf, hx, h⟩, he, ⟨_, hR⟩ => by
    have ih := guards_exact G hG h (by simpa [Holds2, occupied] using he) hR
    rw [← ih]
    simp [guardsT, allT, Holds, Term.denote, hf, Val.toBool]
  | (f, xs) :: S, (true, vs) :: sv, y :: ys, r :: R, ⟨hf, hx, h⟩, he, ⟨hr, hR⟩ => by
    simp only [Holds2, occupied, ite_true, List.filterMap_cons, Forall2] at he
    have ih := guards_exact G hG h he.2 hR
    have hy := hG _ r y hr (by rw [hx]; exact he.1)
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [← ih, ← hy]
    simp [guardsT, allT, Holds, Term.denote, hf, Val.toBool]
  | (_, _) :: _, (true, _) :: _, [], _, _, he, _ => by simp [Holds2, occupied, Forall2] at he


/-- `table.insert` on slots finds a slot exactly when the table it gives fits them. -/
theorem put_exact {k w : Ty} (hk : k.eqable = true) {t0 : (Ty.table k w).den} {S : List Slot}
    {sv : List (Bool × List Val)} {ys : List (k.den × w.den)} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = 2)
    (hperm : ys.Perm t0.1) (hh : Holds2 (ETab L k w) ys sv) (key : k.den) (val : w.den) (kt vt : Term)
    (hkt : RelV L k key (kt.denote M)) :
    Holds M (putSlots S kt vt).2 ↔ (Builtin.tableInsert key val t0).1.length ≤ sv.length := by
  have ha := keep_aligned hk key kt hkt hS hh
  obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
  have hl' : sv'.length = sv.length := by simpa using congrArg List.length hsnd
  have hw' : ∀ p ∈ sv', p.2.length = [kt, vt].length := fun p hp' => by
    have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
    obtain ⟨q, hq, e⟩ := List.mem_map.1 this
    rw [← e]; exact hw q hq
  have hins := insert_exact hS' hw' (p := tt) rfl
  simp only [putSlots]
  rw [hins, ← holds2_length hh', hl']
  have hlen : (ys.filter fun e => !(k.deq key e.1 || k.deq e.1 key)).length =
      (Builtin.tableRemove key t0).1.length := (hperm.filter _).length_eq
  simp only [Builtin.tableInsert, List.length_append, List.length_singleton]
  rw [← hlen]
  omega

/-- `table.from_list` on a list's slots finds a slot for each insertion exactly when every table it builds on its
way fits. -/
theorem putFrom_exact {k w : Ty} (hk : k.eqable = true) (d dt dp : Nat)
    (hdp : ∃ m, L.find? (.tuple [k, w]) = some (dp, m)) :
    {P : List Slot} → {lv : List (Bool × List Val)} → SlotsDen M P lv → (∀ p ∈ lv, p.2.length = 1) →
    {pairs : List (Ty.tuple [k, w]).den} → Holds2 (EBag L (.tuple [k, w])) pairs lv →
    {t0 : (Ty.table k w).den} → {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List (k.den × w.den)} →
    SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 2) → ys.Perm t0.1 → Holds2 (ETab L k w) ys sv →
    (Holds M (putFrom d dt dp S P).2 ↔ insertsFit sv.length pairs t0)
  | [], [], _, _, pairs, hpr, t0, S, sv, ys, hS, hw, hp, hh => by
    have : pairs = [] := by cases pairs <;> simp_all [Holds2, occupied, Forall2]
    subst this
    exact ⟨fun _ => trivial, fun _ => holds_tt⟩
  | (f, xs) :: P, (b, vs) :: lv, ⟨hf, hxs, hP⟩, hlw, pairs, hpr, t0, S, sv, ys, hS, hw, hp, hh => by
    simp only [putFrom]
    rw [holds_andT]
    have hlw' : ∀ p ∈ lv, p.2.length = 1 := fun p hp => hlw p (by simp [hp])
    have hl1 := hlw (b, vs) (by simp)
    obtain ⟨x0, rfl, hx0⟩ : ∃ x0, xs = [x0] ∧ x0.denote M = vs.headD (.bool true) := by
      match xs, vs, hxs, hl1 with
      | [x0], [z], h, _ => exact ⟨x0, rfl, by simpa [Term.denotes] using h⟩
    have hT : ∀ {sv1 : List (Bool × List Val)} {ys1 : List (k.den × w.den)} {t1 : (Ty.table k w).den},
        SlotsDen M (iteSlots f (putSlots S (.sel dp 0 0 ([x0].headD tt)) (.sel dp 0 1 ([x0].headD tt))).1 S) sv1 →
        sv1.length = sv.length → (∀ p ∈ sv1, p.2.length = 2) → ys1.Perm t1.1 → Holds2 (ETab L k w) ys1 sv1 →
        {pairs' : List (Ty.tuple [k, w]).den} → Holds2 (EBag L (.tuple [k, w])) pairs' lv →
        (Holds M (putFrom d dt dp (slotsOf d dt (iteSlots f (putSlots S (.sel dp 0 0 ([x0].headD tt))
            (.sel dp 0 1 ([x0].headD tt))).1 S).length 2 (slotsTerm d dt (iteSlots f (putSlots S
            (.sel dp 0 0 ([x0].headD tt)) (.sel dp 0 1 ([x0].headD tt))).1 S))) P).2 ↔
          insertsFit sv.length pairs' t1) := by
      intro sv1 ys1 t1 hS1 hl1 hw1 hp1 hh1 pairs' hpr'
      have hlen := slotsDen_length hS1
      have hS1' := slotsOf_den d dt 2 _ sv1 (slotsTerm_den d dt hS1) hw1
      rw [← hlen] at hS1'
      rw [← hl1]
      exact putFrom_exact hk d dt dp hdp hP hlw' hpr' hS1' hw1 hp1 hh1
    cases b with
    | true =>
      match pairs, hpr with
      | (key, val, ()) :: pairs', ⟨⟨z, hz, he⟩, hrest⟩ =>
        subst hz
        obtain ⟨m, hfd⟩ := hdp
        obtain ⟨d', n', vals, hf', ev, zk, rest, e1, hzk, zv, rest', e2, hzv, e3⟩ := he
        obtain rfl := find_det hfd hf'
        subst e1 e2
        simp only [RelVs] at e3; subst e3
        simp only [List.headD_cons] at hx0
        have hk' : RelV L k key (Term.denote M (.sel dp 0 0 x0)) := by rw [sel_ctor 0 (hx0.trans ev)]; exact hzk
        have hv' : RelV L w val (Term.denote M (.sel dp 0 1 x0)) := by rw [sel_ctor 1 (hx0.trans ev)]; exact hzv
        have hput := put_exact hk hS hw hp hh key val _ (.sel dp 0 1 x0) hk'
        have hite : Holds M (.ite f (putSlots S (.sel dp 0 0 x0) (.sel dp 0 1 x0)).2 tt) ↔
            Holds M (putSlots S (.sel dp 0 0 x0) (.sel dp 0 1 x0)).2 := by
          simp [holds_ite, hf, Val.toBool]
        simp only [List.headD_cons] at hT ⊢
        rw [hite, hput]
        show (_ ∧ _) ↔ (_ ∧ _)
        constructor
        · rintro ⟨hc1, hc2⟩
          obtain ⟨sv1, ys1, hS1, hl1, hw1, hp1, hh1⟩ := put_den hk hS hw hp hh key val _ _ hk' hv' (hput.2 hc1)
          have hI := iteSlots_den hf hS1 hS hw1 hw hl1
          simp only [ite_true] at hI
          exact ⟨hc1, (hT hI hl1 hw1 hp1 hh1 hrest).1 hc2⟩
        · rintro ⟨hc1, hc2⟩
          obtain ⟨sv1, ys1, hS1, hl1, hw1, hp1, hh1⟩ := put_den hk hS hw hp hh key val _ _ hk' hv' (hput.2 hc1)
          have hI := iteSlots_den hf hS1 hS hw1 hw hl1
          simp only [ite_true] at hI
          exact ⟨hc1, (hT hI hl1 hw1 hp1 hh1 hrest).2 hc2⟩
    | false =>
      obtain ⟨svp, hSp, hlp, hwp⟩ := putSlots_any hS hw (.sel dp 0 0 x0) (.sel dp 0 1 x0)
      have hI := iteSlots_den hf hSp hS hwp hw hlp
      simp only [Bool.false_eq_true, ite_false] at hI
      have hite : Holds M (.ite f (putSlots S (.sel dp 0 0 x0) (.sel dp 0 1 x0)).2 tt) := by
        simp [holds_ite, hf, Val.toBool, holds_tt]
      simp only [List.headD_cons] at hT ⊢
      rw [hT hI rfl hw hp hh (by simpa [Holds2, occupied] using hpr)]
      exact ⟨fun h => h.2, fun h => ⟨hite, h⟩⟩
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _, _, _, _, _, _ => h.elim

end


section
variable (M : Model) (L : Layout)

mutual
/-- A value's code agrees with what the value carries: for a function, at related arguments, the code's condition
holds exactly when the application fits, and where it holds the results agree too. Data carries nothing. -/
def FRel : (t : Ty) → t.den → FT t → Code t → Prop
  | .fn ps r, f, φ, sf => ∀ xs φs ss, Rels M L ps xs ss → FRels ps xs φs ss → ∀ s c, sf ss = .ok (s, c) →
      (Holds M c ↔ (φ xs φs).1) ∧ (Holds M c → FRel r (f xs) (φ xs φs).2 s)
  | .dsl _ _, _, _, _ | .list _, _, _, _ | .int, _, _, _ | .str, _, _, _ | .tuple _, _, _, _ | .adt .., _, _, _
  | .param _, _, _, _ | .bag _, _, _, _ | .table .., _, _, _ | .date, _, _, _ | .id, _, _, _ => True
def FRels : (ts : List Ty) → Ty.dens ts → FTs ts → Codes ts → Prop
  | [], _, _, _ => True
  | t :: ts, (x, xs), (φ, φs), (s, ss) => FRel t x φ s ∧ FRels ts xs φs ss
end

end

/-- Whether a type is a function type. -/
def _root_.Tazuna.Ir.Ty.isFn : Ty → Bool
  | .fn .. => true
  | _ => false

section
variable {M : Model} {L : Layout}

theorem frel_of_notFn : {t : Ty} → t.isFn = false → (x : t.den) → (φ : FT t) → (s : Code t) → FRel M L t x φ s
  | .fn .., h, _, _, _ => nomatch h
  | .dsl _ _, _, _, _, _ | .list _, _, _, _, _ | .int, _, _, _, _ | .str, _, _, _, _ | .tuple _, _, _, _, _
  | .adt .., _, _, _, _ | .param _, _, _, _, _ | .bag _, _, _, _, _ | .table .., _, _, _, _ | .date, _, _, _, _
  | .id, _, _, _, _ => trivial

theorem frels_of_notFn : {ts : List Ty} → (∀ t ∈ ts, t.isFn = false) → (xs : Ty.dens ts) → (φs : FTs ts) →
    (ss : Codes ts) → FRels M L ts xs φs ss
  | [], _, _, _, _ => trivial
  | _ :: _, h, (x, xs), (φ, φs), (s, ss) =>
    ⟨frel_of_notFn (h _ (by simp)) x φ s, frels_of_notFn (fun t ht => h t (by simp [ht])) xs φs ss⟩

theorem ofTerm_notFn : {t : Ty} → {x : Term} → {s : Code t} → Code.ofTerm? t x = some s → t.isFn = false
  | .fn .., _, _, h => nomatch h
  | .dsl _ _, _, _, _ | .list _, _, _, _ | .int, _, _, _ | .str, _, _, _ | .tuple _, _, _, _ | .adt .., _, _, _
  | .param _, _, _, _ | .bag _, _, _, _ | .table .., _, _, _ | .date, _, _, _ | .id, _, _, _ => rfl

theorem term_notFn : {t : Ty} → {s : Code t} → {x : Term} → Code.term? t s = some x → t.isFn = false
  | .fn .., _, _, h => nomatch h
  | .dsl _ _, _, _, _ | .list _, _, _, _ | .int, _, _, _ | .str, _, _, _ | .tuple _, _, _, _ | .adt .., _, _, _
  | .param _, _, _, _ | .bag _, _, _, _ | .table .., _, _, _ | .date, _, _, _ | .id, _, _, _ => rfl

theorem ofTerms_notFn : {ts : List Ty} → {xs : List Term} → {ss : Codes ts} → Codes.ofTerms? ts xs = some ss →
    ∀ t ∈ ts, t.isFn = false
  | [], _, _, _ => by simp
  | t :: ts, x :: xs, ss, h => by
    simp only [Codes.ofTerms?] at h
    cases h1 : Code.ofTerm? t x with
    | none => simp [h1] at h
    | some s =>
      cases h2 : Codes.ofTerms? ts xs with
      | none => simp [h1, h2] at h
      | some ss' =>
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ofTerm_notFn h1
        · exact ofTerms_notFn h2 u hu
  | _ :: _, [], _, h => nomatch h

theorem frel_share : {t : Ty} → {x : t.den} → {φ : FT t} → {s : Code t} → FRel M L t x φ s →
    FRel M L t x φ (Code.share t s)
  | .fn .., _, _, _, h => h
  | .dsl _ _, _, _, _, _ | .list _, _, _, _, _ | .int, _, _, _, _ | .str, _, _, _, _ | .tuple _, _, _, _, _
  | .adt .., _, _, _, _ | .param _, _, _, _, _ | .bag _, _, _, _, _ | .table .., _, _, _, _ | .date, _, _, _, _
  | .id, _, _, _, _ => trivial

theorem frels_share : {ts : List Ty} → {xs : Ty.dens ts} → {φs : FTs ts} → {ss : Codes ts} → FRels M L ts xs φs ss →
    FRels M L ts xs φs (Codes.share ts ss)
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, _, ⟨h, hs⟩ => ⟨frel_share h, frels_share hs⟩

theorem var_frel : {Γ : List Ty} → {t : Ty} → (v : Var Γ t) → (ρ : Ty.dens Γ) → (φ : FTs Γ) → (σ : Codes Γ) →
    FRels M L Γ ρ φ σ → FRel M L t (v.get ρ) (v.ft φ) (v.code σ)
  | _ :: _, _, .here, (_, _), (_, _), (_, _), ⟨h, _⟩ => h
  | _ :: _, _, .there v, (_, _), (_, _), (_, _), ⟨_, h⟩ => var_frel v _ _ _ h

theorem frels_append : {a b : List Ty} → (x : Ty.dens a) → (y : Ty.dens b) → (φ : FTs a) → (ψ : FTs b) →
    (s : Codes a) → (t : Codes b) → FRels M L a x φ s → FRels M L b y ψ t →
    FRels M L (a ++ b) (Dens.append x y) (FTs.append φ ψ) (Codes.append s t)
  | [], _, _, _, _, _, _, _, _, h => h
  | _ :: _, _, (_, _), _, (_, _), _, (_, _), _, ⟨h1, h2⟩, h => ⟨h1, frels_append _ _ _ _ _ _ h2 h⟩

mutual
theorem encodePat_notFn {t : Ty} {Δ : List Ty} : (p : Pat t Δ) → t.isFn = false → (s : Code t) → (m : Term) →
    (δs : Codes Δ) → encodePat L p s = .ok (m, δs) → ∀ u ∈ Δ, u.isFn = false
  | .wild, _, _, _, _, _ => by simp
  | .bind, ht, _, _, _, _ => by simpa using ht
  | .int _, _, _, _, _, _ => by simp
  | .str _, _, _, _, _, _ => by simp
  | @Pat.tuple ts _ ps, _, s, m, δs, h => by
    simp only [encodePat] at h
    obtain ⟨d, -, h⟩ := bind_ok.1 h
    obtain ⟨fs, h2, h⟩ := bind_ok.1 h
    exact encodePats_notFn ps (ofTerms_notFn (need_ok.1 h2)) fs m δs h
  | @Pat.ctor _ _ vs _ v ps, _, s, m, δs, h => by
    simp only [encodePat] at h
    obtain ⟨⟨m1, fts⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨fs, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨m', δ⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact encodePats_notFn ps (ofTerms_notFn (need_ok.1 h2)) fs m' δ h3
  | .as p, ht, s, m, δs, h => by
    simp only [encodePat] at h
    obtain ⟨⟨m1, δ⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact encodePat_notFn p ht s m1 δ h1 u hu
    · simp at hu; subst hu; exact ht
theorem encodePats_notFn {ts : List Ty} {Δ : List Ty} : (ps : Pats ts Δ) → (∀ t ∈ ts, t.isFn = false) →
    (ss : Codes ts) → (m : Term) → (δs : Codes Δ) → encodePats L ps ss = .ok (m, δs) → ∀ u ∈ Δ, u.isFn = false
  | .nil, _, _, _, _, _ => by simp
  | .cons p ps, hts, (s, ss), m, δs, h => by
    simp only [encodePats] at h
    obtain ⟨⟨m1, δ1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨m2, δ2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact encodePat_notFn p (hts _ (by simp)) s m1 δ1 h1 u hu
    · exact encodePats_notFn ps (fun t ht => hts t (by simp [ht])) ss m2 δ2 h2 u hu
end

/-- A pattern's bindings agree with what they carry: a variable bound to the whole value carries what it does, and
every other binding is data. -/
theorem encodePat_frel {t : Ty} {Δ : List Ty} : (p : Pat t Δ) → (x : t.den) → (φ : FT t) → (s : Code t) →
    FRel M L t x φ s → (m : Term) → (δs : Codes Δ) → encodePat L p s = .ok (m, δs) → ∀ δ, p.match x = some δ →
    FRels M L Δ δ (p.fts φ) δs
  | .wild, _, _, _, _, _, _, _, _, _ => trivial
  | .bind, _, _, _, hx, _, _, h, δ, hδ => by cases h; cases hδ; exact ⟨hx, trivial⟩
  | .int _, _, _, _, _, _, _, _, _, _ => trivial
  | .str _, _, _, _, _, _, _, _, _, _ => trivial
  | @Pat.tuple ts _ ps, x, φ, s, _, m, δs, h, δ, _ =>
    frels_of_notFn (encodePat_notFn (.tuple ps) rfl s m δs h) _ _ _
  | @Pat.ctor _ _ vs _ v ps, x, φ, s, _, m, δs, h, δ, _ =>
    frels_of_notFn (encodePat_notFn (.ctor v ps) rfl s m δs h) _ _ _
  | .as p, x, φ, s, hx, m, δs, h, δ, hδ => by
    simp only [encodePat] at h
    obtain ⟨⟨m1, δ1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    simp only [Pat.match] at hδ
    cases hpm : p.match x with
    | none => simp [hpm] at hδ
    | some δ' =>
      simp only [hpm, Option.map_some, Option.some.injEq] at hδ
      subst hδ
      exact frels_append _ _ _ _ _ _ (encodePat_frel p x φ s hx m1 δ1 h1 δ' hpm) ⟨hx, trivial⟩

end


section
variable {M : Model} {L : Layout}

/-- A function whose code's condition is always true and whose result is data agrees with fitting everywhere. -/
theorem frel_tt {ps : List Ty} {r : Ty} (hr : r.isFn = false) {f : (Ty.fn ps r).den} {sf : Code (.fn ps r)}
    (htt : ∀ ss s c, sf ss = .ok (s, c) → c = tt) : FRel M L (.fn ps r) f (FT.dflt _) sf := by
  intro xs φs ss _ _ s c h
  cases htt ss s c h
  exact ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => frel_of_notFn hr _ _ _⟩

theorem allFit_perm {α : Type} {P : α → Prop} {ys xs : List α} (hp : ys.Perm xs) :
    (∀ y ∈ ys, P y) ↔ allFit xs P :=
  ⟨fun h x hx => h x (hp.mem_iff.2 hx), fun h y hy => h y (hp.mem_iff.1 hy)⟩

/-- A function's code applied slot by slot: the guards of its conditions hold exactly when its application to each
occupied slot's item fits. -/
theorem slotGuards_exact {ps : List Ty} {r : Ty} {f : (Ty.fn ps r).den} {φ : FT (.fn ps r)} {sf : Code (.fn ps r)}
    (hf : FRel M L (.fn ps r) f φ sf) {α : Type} {E : α → List Val → Prop} (toD : α → Ty.dens ps) (toF : FTs ps)
    (hE : ∀ y vs, E y vs → RelVs L ps (toD y) vs) {S : List Slot} {sv : List (Bool × List Val)} {ys : List α}
    {R : List (Term × Term)} (hS : SlotsDen M S sv) (hy : Holds2 E ys sv) (hR : slotTerms sf S = .ok R) :
    Holds M (guardsT S (R.map (·.2))) ↔ ∀ y ∈ ys, (φ (toD y) toF).1 := by
  refine guards_exact _ ?_ hS hy (mapM_ok _ S R hR)
  intro sl r' y hr he
  obtain ⟨⟨v, c⟩, h1, hr⟩ := bind_ok.1 hr
  obtain ⟨t, h2, hr⟩ := bind_ok.1 hr
  cases pure_ok.1 hr
  simp only [slotApply] at h1
  obtain ⟨cs, h3, h1⟩ := bind_ok.1 h1
  have hcs := rels_ofTerms (need_ok.1 h3) (toD y) (hE y _ he)
  exact (hf (toD y) toF cs hcs (frels_of_notFn (ofTerms_notFn (need_ok.1 h3)) _ _ _) v c h1).1

/-- Every built-in's code agrees with what it carries: its condition holds exactly when its application fits. -/
theorem primCode_exact (p : Prim) (args : List Ty) (hp : p.ok args = true) (s : Code (p.ty.inst args))
    (h : primCode L p args hp = .ok s) : FRel M L (p.ty.inst args) (p.den args hp) (p.fits L.count args hp) s := by
  cases p
  case length =>
    simp only [primCode] at h; cases h
    exact frel_tt rfl fun ss s c hr => by cases hr; rfl
  case dateAddDays =>
    simp only [primCode] at h; cases h
    exact frel_tt rfl fun ss s c hr => by cases hr; rfl
  case dateDaysBetween =>
    simp only [primCode] at h; cases h
    exact frel_tt rfl fun ss s c hr => by cases hr; rfl
  case require =>
    simp only [primCode] at h; cases h
    intro ⟨b, rej, next, ()⟩ ⟨_, _, φn, ()⟩ ⟨sb, srej, snext, ()⟩ ⟨hb, hrej, hnext, _⟩ ⟨_, _, hfn, _⟩ r c hr
    obtain ⟨⟨v, c1⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨t, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨err, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    have hb' := (rel_bool _ _).1 hb
    have hv := (hfn () () () trivial trivial v c1 h1).1
    have hite : Holds M (.ite sb c1 tt) ↔ if Ty.toBool b = true then Holds M c1 else True := by
      by_cases hbt : Ty.toBool b = true
      · simp only [Holds, Term.denote, hb', hbt, Val.toBool, ite_true]
      · simp [Holds, Term.denote, hb', hbt, Val.toBool, tt]
    refine ⟨hite.trans ?_, fun _ => trivial⟩
    show _ ↔ (if Ty.toBool b = true then (φn () ()).1 else True)
    by_cases hbt : Ty.toBool b = true
    · simp only [hbt, ite_true]; exact hv
    · simp only [hbt, Bool.false_eq_true, ite_false]
  case tableGet =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨kt, -, hr⟩ := bind_ok.1 hr
    obtain ⟨_, -, hr⟩ := bind_ok.1 hr
    obtain ⟨_, -, hr⟩ := bind_ok.1 hr
    obtain ⟨_, -, hr⟩ := map_ok.1 hr
    cases hr; rfl
  case tableLookup =>
    simp only [primCode] at h; cases h
    intro ⟨tb, key, rej, next, ()⟩ ⟨_, _, _, φn, ()⟩ ⟨st, sk, srej, snext, ()⟩ ⟨ht, hk, hrej, hnext, _⟩
      ⟨_, _, _, hfn, _⟩ r c hr
    obtain ⟨kt, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨hit, found⟩, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨fc, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨v, c1⟩, h4, hr⟩ := bind_ok.1 hr
    obtain ⟨rt, h5, hr⟩ := bind_ok.1 hr
    obtain ⟨err, h6, hr⟩ := map_ok.1 hr
    cases hr
    obtain ⟨hhit, hval⟩ := lookup_rel ht key kt ((rel_term (need_ok.1 h1) _).1 hk) h2
    refine ⟨?_, fun _ => trivial⟩
    show Holds M (.ite hit c1 tt) ↔ (match lookupBy (Ty.deq _) key tb.1 with
      | .some v => (φn (v, ()) (FT.dflt _, ())).1
      | .none => True)
    rw [holds_ite]
    cases hl : lookupBy (Ty.deq _) key tb.1 with
    | none =>
      simp only [hl, Option.isSome_none] at hhit
      simp only [hhit, Val.toBool, Bool.false_eq_true, ite_false]
      exact ⟨fun _ => trivial, fun _ => holds_tt⟩
    | some val =>
      simp only [hl, Option.isSome_some] at hhit
      simp only [hhit, Val.toBool, ite_true]
      exact (hfn (val, ()) (FT.dflt _, ()) (fc, ()) ⟨(rel_ofTerm (need_ok.1 h3) _).2 (hval val hl), trivial⟩
        ⟨frel_of_notFn (ofTerm_notFn (need_ok.1 h3)) _ _ _, trivial⟩ v c1 h4).1
  case bagSize =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨_, -, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr; rfl
  case bagFilter | bagCount | bagSum | bagAny | bagAll =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨_, φf, ()⟩ ⟨b, sf, ()⟩ ⟨hb, _, _⟩ ⟨_, hff, _⟩ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    refine ⟨?_, fun _ => trivial⟩
    rw [slotGuards_exact hff (fun y => (y, ())) (FT.dflt _, ()) eBag_rels hS hh h2]
    exact allFit_perm hperm
  case bagMinBy | bagMaxBy =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨_, φf, ()⟩ ⟨b, sf, ()⟩ ⟨hb, _, _⟩ ⟨_, hff, _⟩ r c hr
    simp only [pickCode] at hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    repeat (obtain ⟨_, -, hr⟩ := bind_ok.1 hr)
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    refine ⟨?_, fun _ => trivial⟩
    rw [slotGuards_exact hff (fun y => (y, ())) (FT.dflt _, ()) eBag_rels hS hh h2]
    exact allFit_perm hperm
  case bagMap =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨_, φf, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ ⟨_, hff, _⟩ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨r', c'⟩, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have hg := slotGuards_exact hff (fun y => (y, ())) (FT.dflt _, ()) eBag_rels hS hh h2
    have hlen : ∀ (hgd : Holds M (guardsT (slotsOf d dt n 1 b) (R.map (·.2)))),
        (Holds M c' ↔ xs.length ≤ L.count (.bag ((Ty.param 1).inst args))) := by
      intro hgd
      have ha := slotTerms_aligned hf (fun y => (y, ())) eBag_rels hS hh h2 hgd
      obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := EBag L _) (fun y => f (y, ())) (fun _ q => [q]) 1
        (fun _ _ _ _ hq => ⟨_, rfl, hq⟩) (fun _ _ => rfl) ha
      rw [collOf_exact h3 hS1 hw1, ← holds2_length hh1, List.length_map, hperm.length_eq]
    refine ⟨(holds_andT _ _).trans ?_, fun _ => trivial⟩
    show _ ↔ (allFit xs (fun x => (φf (x, ()) (FT.dflt _, ())).1) ∧
      xs.length ≤ L.count (.bag ((Ty.param 1).inst args)))
    constructor
    · rintro ⟨hgd, hc'⟩
      exact ⟨(allFit_perm hperm).1 (hg.1 hgd), (hlen hgd).1 hc'⟩
    · rintro ⟨hall, hle⟩
      have hgd := hg.2 ((allFit_perm hperm).2 hall)
      exact ⟨hgd, (hlen hgd).2 hle⟩
  case tableFilter | tableCount | tableAny | tableAll =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨_, φf, ()⟩ ⟨b, sf, ()⟩ ⟨hb, _, _⟩ ⟨_, hff, _⟩ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    refine ⟨?_, fun _ => trivial⟩
    rw [slotGuards_exact hff (fun e => (e.1, e.2, ())) (FT.dflt _, FT.dflt _, ()) eTab_rels hS hh h2]
    exact allFit_perm hperm
  case tableMap =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨_, φf, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ ⟨_, hff, _⟩ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨r', c'⟩, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have hg := slotGuards_exact hff (fun e => (e.1, e.2, ())) (FT.dflt _, FT.dflt _, ()) eTab_rels hS hh h2
    have hlen : ∀ (hgd : Holds M (guardsT (slotsOf d dt n 2 b) (R.map (·.2)))),
        (Holds M c' ↔ x.1.length ≤ L.count (.table ((Ty.param 0).inst args) ((Ty.param 2).inst args))) := by
      intro hgd
      have ha := slotTerms_aligned hf (fun e => (e.1, e.2, ())) eTab_rels hS hh h2 hgd
      obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := ETab L _ _) (fun e => (e.1, f (e.1, e.2, ())))
        (fun xs q => [xs.headD q, q]) 2 (fun e xs q he hq => by
          obtain ⟨zk, zv, hxs, hzk, -⟩ := he
          match xs, hxs with
          | [tk, tv], hxs =>
            simp only [Term.denotes, List.cons.injEq] at hxs
            exact ⟨zk, _, by simp [Term.denotes, hxs.1], hzk, hq⟩) (fun _ _ => rfl) ha
      rw [collOf_exact h3 hS1 hw1, ← holds2_length hh1, List.length_map, hperm.length_eq]
    refine ⟨(holds_andT _ _).trans ?_, fun _ => trivial⟩
    show _ ↔ (allFit x.1 (fun e => (φf (e.1, e.2, ()) (FT.dflt _, FT.dflt _, ())).1) ∧
      x.1.length ≤ L.count (.table ((Ty.param 0).inst args) ((Ty.param 2).inst args)))
    constructor
    · rintro ⟨hgd, hc'⟩
      exact ⟨(allFit_perm hperm).1 (hg.1 hgd), (hlen hgd).1 hc'⟩
    · rintro ⟨hall, hle⟩
      have hgd := hg.2 ((allFit_perm hperm).2 hall)
      exact ⟨hgd, (hlen hgd).2 hle⟩
  case tableKeys =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨_, ()⟩ ⟨b, ()⟩ ⟨hb, _⟩ _ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha : AlignedV M (ETab L _ _) (fun _ _ => True) _ _ sv ys := aligned_map (fun _ => tt) (fun _ _ _ => trivial) hS hh
    obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := fun (_ : Unit) (vs : List Val) => vs.length = 1)
      (fun _ => ()) (fun xs q => [xs.headD q]) 1 (fun _ _ _ _ _ => by simp [Term.denotes]) (fun _ _ => rfl) ha
    refine ⟨?_, fun _ => trivial⟩
    rw [collOf_exact hr hS1 hw1, ← holds2_length hh1, List.length_map, hperm.length_eq]
    rfl
  case tableValues =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨_, ()⟩ ⟨b, ()⟩ ⟨hb, _⟩ _ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha : AlignedV M (ETab L _ _) (fun _ _ => True) _ _ sv ys := aligned_map (fun _ => tt) (fun _ _ _ => trivial) hS hh
    obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := fun (_ : Unit) (vs : List Val) => vs.length = 1)
      (fun _ => ()) (fun xs q => [xs.getD 1 q]) 1 (fun _ _ _ _ _ => by simp [Term.denotes]) (fun _ _ => rfl) ha
    refine ⟨?_, fun _ => trivial⟩
    rw [collOf_exact hr hS1 hw1, ← holds2_length hh1, List.length_map, hperm.length_eq]
    rfl
  case tableSize =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨_, -, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr; rfl
  case tableNew =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨_, -, hr⟩ := bind_ok.1 hr
    obtain ⟨_, -, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr; rfl
  case tableRemove =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    repeat (obtain ⟨_, -, hr⟩ := bind_ok.1 hr)
    cases pure_ok.1 hr; rfl
  case bagContains =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    repeat (obtain ⟨_, -, hr⟩ := bind_ok.1 hr)
    cases pure_ok.1 hr; rfl
  case fresh =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    repeat (obtain ⟨_, -, hr⟩ := bind_ok.1 hr)
    cases pure_ok.1 hr; rfl
  case bagInsert =>
    simp only [primCode] at h; cases h
    intro ⟨xs, x, ()⟩ _ ⟨b, sx, ()⟩ ⟨hb, hx, _⟩ _ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨xt, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := bag_view hb h1
    refine ⟨?_, fun _ => trivial⟩
    rw [insert_exact hS (x := [xt]) hw rfl, ← holds2_length hh, hperm.length_eq, hl]
    show _ ↔ xs.length + 1 ≤ L.count (.bag ((Ty.param 0).inst args))
    have := collD_count h1
    omega
  case tableInsert =>
    simp only [primCode] at h; cases h
    intro ⟨x, key, val, ()⟩ _ ⟨b, sk, sv0, ()⟩ ⟨hb, hk, hv, _⟩ _ r c hr
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨kt0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨kt, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨vt, h4, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view hb h1
    refine ⟨?_, fun _ => trivial⟩
    rw [put_exact heq hS hw hperm hh key val kt vt ((rel_term (need_ok.1 h2) key).1 hk), hl]
    show _ ↔ _ ≤ L.count (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
    have := collD_count h1
    omega
  case bagFromList =>
    simp only [primCode] at h; cases h
    intro ⟨xs, ()⟩ _ ⟨items, ()⟩ ⟨hxs, _⟩ _ r c hr
    change Rel M L (.list ((Ty.param 0).inst args)) xs items at hxs
    obtain ⟨⟨dl, nl, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨sv, hS, -, hw, hh⟩ := list_view hxs h1
    refine ⟨?_, fun _ => trivial⟩
    rw [collOf_exact hr hS hw, ← holds2_length hh]
    rfl
  case tableFromList =>
    simp only [primCode] at h; cases h
    intro ⟨pairs, ()⟩ _ ⟨ps, ()⟩ ⟨hps, _⟩ _ r c hr
    change Rel M L (.list (.tuple [(Ty.param 0).inst args, (Ty.param 1).inst args])) pairs ps at hps
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨dl, nl, dtl⟩, h1', hr⟩ := bind_ok.1 hr
    obtain ⟨dp0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨dp, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨S0, h4, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    obtain ⟨m, hdp⟩ := tupleD_ok h2
    simp only [emptySlots] at h4
    obtain ⟨dx, h5, h4⟩ := bind_ok.1 h4
    cases pure_ok.1 h4
    have hdl : dx.length = 2 := by
      have := need_ok.1 h5
      simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind, pure] at this
      split at this <;> try cases this
      split at this <;> try cases this
      all_goals rfl
    obtain ⟨lv, hP, -, hlw, hlh⟩ := list_view hps h1'
    refine ⟨?_, fun _ => trivial⟩
    rw [putFrom_exact heq d dt dp ⟨m, hdp⟩ hP hlw hlh (t0 := Builtin.tableEmpty) (empty_den dx n)
      (fun p hp => by simp only [List.mem_replicate] at hp; rw [hp.2, denotes_eq_map]; simpa using hdl)
      (ys := []) (List.Perm.refl _) (by simp [Holds2, occupied_empty, Forall2]), List.length_replicate]
    show _ ↔ insertsFit (L.count (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))) pairs _
    rw [collD_count h1]
  case externalCommand =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨x, _⟩ := ss
    dsimp only at hr
    split at hr
    split at hr
    · simp only [Except.ok.injEq] at hr; exact (congrArg Prod.snd hr).symm
    · cases hr
  case externalQuery =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨x, f, _⟩ := ss
    dsimp only at hr
    split at hr
    split at hr
    · simp only [Except.ok.injEq] at hr; exact (congrArg Prod.snd hr).symm
    · cases hr
  case requestCommand | requestQuery =>
    simp only [primCode] at h; cases h
    refine frel_tt rfl fun ss s c hr => ?_
    obtain ⟨_, _, _, _⟩ := ss
    dsimp only at hr
    obtain ⟨it, -, hr⟩ := bind_ok.1 hr
    obtain ⟨t, -, e⟩ := map_ok.1 hr
    cases e; rfl
  all_goals simp [primCode] at h

end


section
variable {M : Model} {L : Layout}

theorem ite?_notFn {t : Ty} {c : Term} {a b r : Code t} (h : Code.ite? t c a b = some r) : t.isFn = false := by
  cases t <;> first | rfl | simp [Code.ite?, Code.term?] at h

theorem listOf_exact {t : Ty} {ts : List Term} {r c : Term} (h : listOf L t ts = .ok (r, c)) :
    Holds M c ↔ ts.length ≤ L.count (.list t) := by
  obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨dflt, -, h⟩ := bind_ok.1 h
  rw [collD_count h1]
  split at h
  · rename_i hle; cases pure_ok.1 h; exact ⟨fun _ => hle, fun _ => holds_tt⟩
  · rename_i hle; cases pure_ok.1 h
    simp only [Holds, Term.denote, Val.toBool, Bool.false_eq_true, false_iff]; exact hle

variable {G : List Ty} (D : Defs G) (g : Ty.dens G) (gs : Encs G) (gf : GFits G)

theorem encodeItems_length {Γ : List Ty} {t : Ty} : (items : Items G Γ t) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    (ss : List (Code t)) → (c : Term) → encodeItems L gs items σ = .ok (ss, c) →
    ss.length = (Items.eval D g items ρ).length
  | .nil, _, _, ss, c, h => by cases h; rfl
  | .cons e es, σ, ρ, ss, c, h => by
    simp only [encodeItems] at h
    obtain ⟨⟨x, c1⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨xs, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    simp [Items.eval, encodeItems_length es σ ρ xs c2 h2]

theorem clauses_eval_some {Γ : List Ty} {t r : Ty} {sh : List Shape} {Δ : List Ty} (p : Pat t Δ) (body : Expr G (Δ ++ Γ) r)
    (rest : Clauses G Γ t r sh) (ρ : Ty.dens Γ) (x : t.den) (h : ∃ s ∈ p.shape :: sh, Shape.Matches t s x)
    {δ : Ty.dens Δ} (hm : p.match x = some δ) :
    Clauses.eval D g (.cons p body rest) ρ x h = Expr.eval D g body (Dens.append δ ρ) := by
  simp only [Clauses.eval]; split <;> simp_all

theorem clauses_eval_none {Γ : List Ty} {t r : Ty} {sh : List Shape} {Δ : List Ty} (p : Pat t Δ) (body : Expr G (Δ ++ Γ) r)
    (rest : Clauses G Γ t r sh) (ρ : Ty.dens Γ) (x : t.den) (h : ∃ s ∈ p.shape :: sh, Shape.Matches t s x)
    (hm : p.match x = none) :
    Clauses.eval D g (.cons p body rest) ρ x h = Clauses.eval D g rest ρ x (Clauses.skip hm h) := by
  simp only [Clauses.eval]; split <;> simp_all

theorem clauses_fits_some {Γ : List Ty} {t r : Ty} {sh : List Shape} {Δ : List Ty} (p : Pat t Δ)
    (body : Expr G (Δ ++ Γ) r) (rest : Clauses G Γ t r sh) (ρ : Ty.dens Γ) (φ : FTs Γ) (x : t.den) (fx : FT t)
    (h : ∃ s ∈ p.shape :: sh, Shape.Matches t s x) {δ : Ty.dens Δ} (hm : p.match x = some δ) :
    Clauses.fits L.count D g gf (.cons p body rest) ρ φ x fx h =
      Expr.fits L.count D g gf body (Dens.append δ ρ) (FTs.append (p.fts fx) φ) := by
  simp only [Clauses.fits]; split <;> simp_all

theorem clauses_fits_none {Γ : List Ty} {t r : Ty} {sh : List Shape} {Δ : List Ty} (p : Pat t Δ)
    (body : Expr G (Δ ++ Γ) r) (rest : Clauses G Γ t r sh) (ρ : Ty.dens Γ) (φ : FTs Γ) (x : t.den) (fx : FT t)
    (h : ∃ s ∈ p.shape :: sh, Shape.Matches t s x) (hm : p.match x = none) :
    Clauses.fits L.count D g gf (.cons p body rest) ρ φ x fx h =
      Clauses.fits L.count D g gf rest ρ φ x fx (Clauses.skip hm h) := by
  simp only [Clauses.fits]; split <;> simp_all

end

/-- The globals' codes agree with what their values carry, and their conditions with their evaluations' fit. -/
def GFRel (M : Model) (L : Layout) {G : List Ty} (g : Ty.dens G) (gf : GFits G) (gs : Encs G) : Prop :=
  ∀ (t : Ty) (v : Var G t) s c, v.enc gs = .ok (s, c) →
    (Holds M c ↔ (v.gfit gf).1) ∧ (Holds M c → FRel M L t (v.get g) (v.gfit gf).2 s)

section
variable {M : Model} {L : Layout} {G : List Ty} (D : Defs G) (g : Ty.dens G) (gs : Encs G) (gf : GFits G)
  (hg : GRel M L g gs) (hgf : GFRel M L g gf gs)
include hg hgf

set_option linter.unusedSectionVars false

mutual
/-- A code's condition is exact: it holds exactly when the expression's evaluation fits the layout's slot counts,
and where it holds the code agrees with what the value carries. -/
theorem encode_exact {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → (σ : Codes Γ) → (ρ : Ty.dens Γ) → (φ : FTs Γ) →
    Rels M L Γ ρ σ → FRels M L Γ ρ φ σ → (s : Code t) → (c : Term) → encode L gs e σ = .ok (s, c) →
    (Holds M c ↔ (Expr.fits L.count D g gf e ρ φ).1) ∧
      (Holds M c → FRel M L t (e.eval D g ρ) (Expr.fits L.count D g gf e ρ φ).2 s)
  | .int n, _, _, _, _, _, s, c, h => by cases h; exact ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => trivial⟩
  | .str lit, _, _, _, _, _, s, c, h => by
    simp only [encode] at h; split at h
    · cases h; exact ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => trivial⟩
    · cases h
  | .var v, σ, ρ, φ, _, hφ, s, c, h => by
    cases h; exact ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => var_frel v ρ φ σ hφ⟩
  | .global v, _, _, _, _, _, s, c, h => hgf _ v s c h
  | @Expr.ctor _ _ i args vs v es, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨fs, -, h⟩ := bind_ok.1 h
    obtain ⟨t', -, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨(encodes_exact es σ ρ φ hσ hφ ss c1 h1).1, fun _ => trivial⟩
  | @Expr.field _ _ i args vs ft _ k hk e, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    have he := encode_exact e σ ρ φ hσ hφ x c1 h1
    cases i with
    | zero => cases h
    | succ i =>
      simp only at h
      split at h
      · obtain ⟨r, h2, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        exact ⟨he.1, fun _ => frel_of_notFn (ofTerm_notFn (need_ok.1 h2)) _ _ _⟩
      · cases h
  | @Expr.index _ _ ts e k, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨d, -, h⟩ := bind_ok.1 h
    obtain ⟨r, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨(encode_exact e σ ρ φ hσ hφ x c1 h1).1, fun _ => frel_of_notFn (ofTerm_notFn (need_ok.1 h3)) _ _ _⟩
  | @Expr.update _ _ i args fs e p, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    have he := encode_exact e σ ρ φ hσ hφ x c1 h1
    cases i with
    | zero => cases h
    | succ i =>
      simp only at h
      split at h
      · obtain ⟨⟨ys, c2⟩, h2, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        refine ⟨?_, fun _ => trivial⟩
        rw [holds_andT, he.1, encodePatch_exact p σ ρ φ hσ hφ _ 0 ys c2 h2]
        rfl
      · cases h
  | .call f args, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨sf, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨ss, c2⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨r, c3⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have hf := encode_exact f σ ρ φ hσ hφ sf c1 h1
    have ha := encodes_exact args σ ρ φ hσ hφ ss c2 h2
    have happ : ∀ (hc1 : Holds M c1) (hc2 : Holds M c2), _ := fun hc1 hc2 =>
      hf.2 hc1 _ _ _ (rels_share (encodes_agrees D g gs hg args σ ρ hσ ss c2 h2 hc2)) (frels_share (ha.2 hc2)) r c3 h3
    refine ⟨?_, fun hc => ?_⟩
    · rw [holds_andT, holds_andT]
      constructor
      · rintro ⟨hc1, hc2, hc3⟩
        exact ⟨hf.1.1 hc1, ha.1.1 hc2, (happ hc1 hc2).1.1 hc3⟩
      · rintro ⟨p1, p2, p3⟩
        have hc1 := hf.1.2 p1
        have hc2 := ha.1.2 p2
        exact ⟨hc1, hc2, (happ hc1 hc2).1.2 p3⟩
    · obtain ⟨hc1, hc'⟩ := (holds_andT _ _).1 hc
      obtain ⟨hc2, hc3⟩ := (holds_andT _ _).1 hc'
      exact (happ hc1 hc2).2 hc3
  | .lam body, σ, ρ, φ, hσ, hφ, s, c, h => by
    cases h
    refine ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => ?_⟩
    intro xs φs ss hxs hφs r c' hr
    exact encode_exact body (Codes.append ss σ) (Dens.append xs ρ) (FTs.append φs φ) (rels_append _ _ _ _ hxs hσ)
      (frels_append _ _ _ _ _ _ hφs hφ) r c' hr
  | .let_ e body, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨r, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have he := encode_exact e σ ρ φ hσ hφ x c1 h1
    have hb : ∀ (hc1 : Holds M c1), _ := fun hc1 => encode_exact body _ (e.eval D g ρ, ρ)
      ((Expr.fits L.count D g gf e ρ φ).2, φ) ⟨rel_share (encode_agrees D g gs hg e σ ρ hσ x c1 h1 hc1), hσ⟩
      ⟨frel_share (he.2 hc1), hφ⟩ r c2 h2
    refine ⟨?_, fun hc => (hb ((holds_andT _ _).1 hc).1).2 ((holds_andT _ _).1 hc).2⟩
    rw [holds_andT]
    constructor
    · rintro ⟨hc1, hc2⟩; exact ⟨he.1.1 hc1, (hb hc1).1.1 hc2⟩
    · rintro ⟨p1, p2⟩; have hc1 := he.1.2 p1; exact ⟨hc1, (hb hc1).1.2 p2⟩
  | .case e cs hx, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨o, h2, h⟩ := bind_ok.1 h
    cases o with
    | none => cases h
    | some rc =>
      obtain ⟨r, c2⟩ := rc
      cases pure_ok.1 h
      have he := encode_exact e σ ρ φ hσ hφ x c1 h1
      have hb : ∀ (hc1 : Holds M c1), _ := fun hc1 => encodeClauses_exact cs σ ρ φ hσ hφ _ _ _
        (rel_share (encode_agrees D g gs hg e σ ρ hσ x c1 h1 hc1)) (frel_share (he.2 hc1)) (hx.sound _) _ c2 h2
      refine ⟨?_, fun hc => (hb ((holds_andT _ _).1 hc).1).2 ((holds_andT _ _).1 hc).2⟩
      rw [holds_andT]
      constructor
      · rintro ⟨hc1, hc2⟩; exact ⟨he.1.1 hc1, (hb hc1).1.1 hc2⟩
      · rintro ⟨p1, p2⟩; have hc1 := he.1.2 p1; exact ⟨hc1, (hb hc1).1.2 p2⟩
  | @Expr.list _ _ t items, σ, ρ, φ, hσ, hφ, s, c, h => by
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨ts, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨r, c2⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    refine ⟨?_, fun _ => trivial⟩
    rw [holds_andT, encodeItems_exact items σ ρ φ hσ hφ ss c1 h1, listOf_exact h3,
      ← forall2_length (mapM_ok _ ss ts h2), encodeItems_length D g gs items σ ρ ss c1 h1]
    rfl
  | @Expr.tuple _ _ ts es, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨fs, -, h⟩ := bind_ok.1 h
    obtain ⟨d, -, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨(encodes_exact es σ ρ φ hσ hφ ss c1 h1).1, fun _ => trivial⟩
  | .bin op l r, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨y, c2⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨z, -, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    refine ⟨?_, fun _ => frel_of_notFn (by cases op <;> rfl) _ _ _⟩
    rw [holds_andT, (encode_exact l σ ρ φ hσ hφ x c1 h1).1, (encode_exact r σ ρ φ hσ hφ y c2 h2).1]
    rfl
  | .not e, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨(encode_exact e σ ρ φ hσ hφ x _ h1).1, fun _ => trivial⟩
  | .neg e, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨(encode_exact e σ ρ φ hσ hφ x _ h1).1, fun _ => trivial⟩
  | .prim p args hp, _, _, _, _, _, s, c, h => by
    simp only [encode] at h
    obtain ⟨r, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => primCode_exact p args hp _ h1⟩
  | @Expr.close _ _ Γ' _ _ env hΓ _ _, σ, ρ, φ, hσ, hφ, s, c, h => by
    simp only [encode] at h
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨ts, -, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨(encodes_exact env σ ρ φ hσ hφ ss c1 h1).1, fun _ => trivial⟩
  | .closeEffect .., _, _, _, _, _, _, _, h => by simp only [encode] at h; cases h
theorem encodes_exact {Γ : List Ty} {ts : List Ty} : (es : Exprs G Γ ts) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    (φ : FTs Γ) → Rels M L Γ ρ σ → FRels M L Γ ρ φ σ → (ss : Codes ts) → (c : Term) → encodes L gs es σ = .ok (ss, c) →
    (Holds M c ↔ (Exprs.fits L.count D g gf es ρ φ).1) ∧
      (Holds M c → FRels M L ts (Exprs.eval D g es ρ) (Exprs.fits L.count D g gf es ρ φ).2 ss)
  | .nil, _, _, _, _, _, _, _, h => by cases h; exact ⟨⟨fun _ => trivial, fun _ => holds_tt⟩, fun _ => trivial⟩
  | .cons e es, σ, ρ, φ, hσ, hφ, ss, c, h => by
    simp only [encodes] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨xs, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have he := encode_exact e σ ρ φ hσ hφ x c1 h1
    have hes := encodes_exact es σ ρ φ hσ hφ xs c2 h2
    refine ⟨?_, fun hc => ⟨he.2 ((holds_andT _ _).1 hc).1, hes.2 ((holds_andT _ _).1 hc).2⟩⟩
    rw [holds_andT, he.1, hes.1]
    rfl
theorem encodeItems_exact {Γ : List Ty} {t : Ty} : (items : Items G Γ t) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    (φ : FTs Γ) → Rels M L Γ ρ σ → FRels M L Γ ρ φ σ → (ss : List (Code t)) → (c : Term) →
    encodeItems L gs items σ = .ok (ss, c) → (Holds M c ↔ Items.fits L.count D g gf items ρ φ)
  | .nil, _, _, _, _, _, ss, c, h => by cases h; exact ⟨fun _ => trivial, fun _ => holds_tt⟩
  | .cons e es, σ, ρ, φ, hσ, hφ, ss, c, h => by
    simp only [encodeItems] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨xs, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_andT, (encode_exact e σ ρ φ hσ hφ x c1 h1).1, encodeItems_exact es σ ρ φ hσ hφ xs c2 h2]
    rfl
theorem encodePatch_exact {Γ : List Ty} {ts : List Ty} : (p : Patch G Γ ts) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    (φ : FTs Γ) → Rels M L Γ ρ σ → FRels M L Γ ρ φ σ → (keep : Nat → Term) → (j : Nat) → (ys : List Term) →
    (c : Term) → encodePatch L gs p σ keep j = .ok (ys, c) → (Holds M c ↔ Patch.fits L.count D g gf p ρ φ)
  | .nil, _, _, _, _, _, _, _, ys, c, h => by cases h; exact ⟨fun _ => trivial, fun _ => holds_tt⟩
  | .keep rest, σ, ρ, φ, hσ, hφ, keep, j, ys, c, h => by
    simp only [encodePatch] at h
    obtain ⟨⟨zs, c1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact encodePatch_exact rest σ ρ φ hσ hφ keep (j + 1) zs c1 h1
  | .set e rest, σ, ρ, φ, hσ, hφ, keep, j, ys, c, h => by
    simp only [encodePatch] at h
    obtain ⟨⟨s, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨y, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨zs, c2⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_andT, (encode_exact e σ ρ φ hσ hφ s c1 h1).1, encodePatch_exact rest σ ρ φ hσ hφ keep (j + 1) zs c2 h3]
    rfl
theorem encodeClauses_exact {Γ : List Ty} {t r : Ty} {sh : List Shape} : (cs : Clauses G Γ t r sh) →
    (σ : Codes Γ) → (ρ : Ty.dens Γ) → (φ : FTs Γ) → Rels M L Γ ρ σ → FRels M L Γ ρ φ σ → (s : Code t) →
    (x : t.den) → (fx : FT t) → Rel M L t x s → FRel M L t x fx s → (hx : ∃ s ∈ sh, Shape.Matches t s x) →
    (v : Code r) → (c : Term) → encodeClauses L gs cs σ s = .ok (some (v, c)) →
    (Holds M c ↔ (Clauses.fits L.count D g gf cs ρ φ x fx hx).1) ∧
      (Holds M c → FRel M L r (Clauses.eval D g cs ρ x hx) (Clauses.fits L.count D g gf cs ρ φ x fx hx).2 v)
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | .cons p body rest, σ, ρ, φ, hσ, hφ, s, x, fx, hs, hfs, hx, v, c, h => by
    simp only [encodeClauses] at h
    obtain ⟨⟨m, δs⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨vb, cb⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨o, h3, h⟩ := bind_ok.1 h
    obtain ⟨hm, hδ⟩ := encodePat_agrees p x s hs m δs h1
    cases hpm : p.match x with
    | some δ =>
      rw [clauses_eval_some D g p body rest ρ x hx hpm, clauses_fits_some D g gf p body rest ρ φ x fx hx hpm]
      have hb := encode_exact body (Codes.append δs σ) (Dens.append δ ρ) (FTs.append (p.fts fx) φ)
        (rels_append _ _ _ _ (hδ δ hpm) hσ) (frels_append _ _ _ _ _ _ (encodePat_frel p x fx s hfs m δs h1 δ hpm) hφ)
        vb cb h2
      rw [hpm] at hm
      cases o with
      | none => cases pure_ok.1 h; exact hb
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h4, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        have hite : Holds M (.ite m cb cr) ↔ Holds M cb := by simp [holds_ite, hm, Val.toBool]
        exact ⟨hite.trans hb.1, fun _ => frel_of_notFn (ite?_notFn (need_ok.1 h4)) _ _ _⟩
    | none =>
      rw [clauses_eval_none D g p body rest ρ x hx hpm, clauses_fits_none D g gf p body rest ρ φ x fx hx hpm]
      rw [hpm] at hm
      cases o with
      | none => exact absurd (Clauses.skip hpm hx) (by rw [encodeClauses_none rest σ s h3]; simp)
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h4, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        have hite : Holds M (.ite m cb cr) ↔ Holds M cr := by simp [holds_ite, hm, Val.toBool]
        exact ⟨hite.trans (encodeClauses_exact rest σ ρ φ hσ hφ s x fx hs hfs _ vr cr h3).1,
          fun _ => frel_of_notFn (ite?_notFn (need_ok.1 h4)) _ _ _⟩
  | .guarded p guard body rest, σ, ρ, φ, hσ, hφ, s, x, fx, hs, hfs, hx, v, c, h => by
    simp only [encodeClauses] at h
    obtain ⟨⟨m, δs⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨vg, cg⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨vb, cb⟩, h3, h⟩ := bind_ok.1 h
    obtain ⟨o, h4, h⟩ := bind_ok.1 h
    obtain ⟨hm, hδ⟩ := encodePat_agrees p x s hs m δs h1
    simp only [Clauses.eval, Clauses.fits]
    cases hpm : p.match x with
    | some δ =>
      simp only
      have hr := rels_append _ _ _ _ (hδ δ hpm) hσ
      have hf := frels_append _ _ _ _ _ _ (encodePat_frel p x fx s hfs m δs h1 δ hpm) hφ
      have hgd := encode_exact guard (Codes.append δs σ) (Dens.append δ ρ) (FTs.append (p.fts fx) φ) hr hf vg cg h2
      have hb := encode_exact body (Codes.append δs σ) (Dens.append δ ρ) (FTs.append (p.fts fx) φ) hr hf vb cb h3
      rw [hpm] at hm
      have hvg : ∀ (hcg : Holds M cg), vg.denote M = .bool (Ty.toBool (Expr.eval D g guard (Dens.append δ ρ))) :=
        fun hcg => (rel_bool _ _).1 (encode_agrees D g gs hg guard _ _ hr vg cg h2 hcg)
      cases o with
      | none =>
        cases pure_ok.1 h
        by_cases hgt : Ty.toBool (Expr.eval D g guard (Dens.append δ ρ)) = true
        · simp only [hgt, ite_true]
          refine ⟨?_, fun hc => hb.2 ((holds_andT _ _).1 hc).2⟩
          rw [holds_andT, hgd.1, hb.1]
        · exact absurd hx (by rw [encodeClauses_none rest σ s h4]; simp)
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h5, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        have hite : Holds M (.ite m (andT cg (.ite vg cb cr)) cr) ↔ Holds M (andT cg (.ite vg cb cr)) := by
          simp [holds_ite, hm, Val.toBool]
        refine ⟨?_, fun _ => frel_of_notFn (ite?_notFn (need_ok.1 h5)) _ _ _⟩
        rw [hite, holds_andT]
        have hrest := (encodeClauses_exact rest σ ρ φ hσ hφ s x fx hs hfs hx vr cr h4).1
        by_cases hgt : Ty.toBool (Expr.eval D g guard (Dens.append δ ρ)) = true
        · simp only [hgt, ite_true]
          constructor
          · rintro ⟨hcg, hci⟩
            have := (holds_ite _ _ _).1 hci
            rw [hvg hcg] at this
            exact ⟨hgd.1.1 hcg, hb.1.1 (by simpa [Val.toBool, hgt] using this)⟩
          · rintro ⟨p1, p2⟩
            have hcg := hgd.1.2 p1
            refine ⟨hcg, (holds_ite _ _ _).2 ?_⟩
            rw [hvg hcg]; simpa [Val.toBool, hgt] using hb.1.2 p2
        · simp only [hgt, Bool.false_eq_true, ite_false]
          constructor
          · rintro ⟨hcg, hci⟩
            have := (holds_ite _ _ _).1 hci
            rw [hvg hcg] at this
            exact ⟨hgd.1.1 hcg, hrest.1 (by simpa [Val.toBool, hgt] using this)⟩
          · rintro ⟨p1, p2⟩
            have hcg := hgd.1.2 p1
            refine ⟨hcg, (holds_ite _ _ _).2 ?_⟩
            rw [hvg hcg]; simpa [Val.toBool, hgt] using hrest.2 p2
    | none =>
      simp only
      rw [hpm] at hm
      cases o with
      | none => exact absurd hx (by rw [encodeClauses_none rest σ s h4]; simp)
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h5, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        have hite : Holds M (.ite m (andT cg (.ite vg cb cr)) cr) ↔ Holds M cr := by simp [holds_ite, hm, Val.toBool]
        exact ⟨hite.trans (encodeClauses_exact rest σ ρ φ hσ hφ s x fx hs hfs hx vr cr h4).1,
          fun _ => frel_of_notFn (ite?_notFn (need_ok.1 h5)) _ _ _⟩
end

end

theorem envCodes_notFn {L : Layout} : (Γ : List Ty) → (ρ : Ty.dens Γ) → (σ : Codes Γ) → envCodes L Γ ρ = some σ →
    ∀ t ∈ Γ, t.isFn = false
  | [], _, _, _ => by simp
  | t :: Γ, (x, xs), (c, cs), h => by
    cases hw : embedV L t x with
    | none => simp [envCodes, hw] at h
    | some w =>
      cases hc : Code.ofTerm? t w.term with
      | none => simp [envCodes, hw, hc] at h
      | some c' =>
        cases hcs : envCodes L Γ xs with
        | none => simp [envCodes, hw, hcs] at h
        | some cs' =>
          intro u hu
          rcases List.mem_cons.1 hu with rfl | hu
          · exact ofTerm_notFn hc
          · exact envCodes_notFn Γ xs cs' hcs u hu

/-- Every global's condition is exact and its code agrees with what its value carries. -/
theorem Defs.encode_exact (M : Model) (L : Layout) : {G : List Ty} → (defs : Defs G) →
    GFRel M L defs.eval (defs.fits L.count) (defs.encode L)
  | [], .nil => fun _ v => nomatch v
  | _ :: _, .snoc defs _ body => by
    intro t v s c h
    cases v with
    | here =>
      exact Smt.encode_exact defs _ _ _ (Defs.encode_agrees M L defs) (Defs.encode_exact M L defs) body () () () trivial
        trivial s c h
    | there v => exact Defs.encode_exact M L defs t v s c h

/-- A kept function's condition is exact: it holds exactly when its source's evaluation fits, and where it holds its
code agrees with what the function carries. -/
theorem _root_.Tazuna.Ir.Fun.code_exact {M : Model} {L : Layout} {t : Ty} (f : Fun t) {s : Code t} {c : Term}
    (h : f.code L = .ok (s, c)) : (Holds M c ↔ (f.fits L.count).1) ∧ (Holds M c → FRel M L t f.eval (f.fits L.count).2 s) := by
  obtain ⟨σ, hσ, h⟩ := bind_ok.1 h
  have hr := envCodes_rels (M := M) _ _ σ (need_ok.1 hσ)
  exact encode_exact f.defs f.defs.eval (f.defs.encode L) (f.defs.fits L.count) (Defs.encode_agrees M L f.defs)
    (Defs.encode_exact M L f.defs) f.body σ _ _ hr (frels_of_notFn (envCodes_notFn _ _ _ (need_ok.1 hσ)) _ _ _) s c h

/-- The same for a kept function that returns effects. -/
theorem _root_.Tazuna.Ir.EffectFun.code_exact {M : Model} {L : Layout} {ps : List Ty} {r : Ty} (f : EffectFun ps r)
    {s : Code (.fn ps r)} {c : Term} (h : f.code L = .ok (s, c)) :
    (Holds M c ↔ (f.fits L.count).1) ∧
      (Holds M c → FRel M L (.fn ps r) (f.body.eval f.defs f.defs.eval (Ty.up _ f.hΓ f.env)) (f.fits L.count).2 s) := by
  obtain ⟨σ, hσ, h⟩ := bind_ok.1 h
  have hr := envCodes_rels (M := M) _ _ σ (need_ok.1 hσ)
  exact encode_exact f.defs f.defs.eval (f.defs.encode L) (f.defs.fits L.count) (Defs.encode_agrees M L f.defs)
    (Defs.encode_exact M L f.defs) f.body σ _ _ hr (frels_of_notFn (envCodes_notFn _ _ _ (need_ok.1 hσ)) _ _ _) s c h

end Tazuna.Smt
