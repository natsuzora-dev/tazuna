import Tazuna.Smt.Term

/-! Bags and tables as slots. A collection of type `c` is a value of datatype `d` with one constructor holding `n`
slots, the slot count its layout gives `c`; each slot is a tuple `(occupied, item...)` of datatype `dt`, with one item
term for a bag and a key and a value for a table. The collection is the items of the occupied slots, in any order:
bags and tables have no order a spec can observe. Operations work slot by slot, so their terms stay quantifier-free;
an insertion takes the first free slot, and its condition says one was free. -/

namespace Tazuna.Smt

/-- A slot's occupied flag and its item terms. -/
abbrev Slot := Term × List Term

def tt : Term := .bool true

/-- The `n` slots of the collection `s`, each with `w` item terms. They select from `s` `n * (w + 1)` times, so `s`
is shared. -/
def slotsOf (d dt n w : Nat) (s : Term) : List Slot :=
  (List.range n).map fun i =>
    let x := Term.sel d 0 i s.share
    (.sel dt 0 0 x, (List.range w).map fun j => .sel dt 0 (j + 1) x)

/-- The collection holding these slots, shared: the next operation on it selects each slot. -/
def slotsTerm (d dt : Nat) (S : List Slot) : Term := Term.share (.ctor d 0 (S.map fun (f, xs) => .ctor dt 0 (f :: xs)))

def sumT : List Term → Term
  | [] => .int 0
  | a :: r => .add a (sumT r)

def anyT : List Term → Term
  | [] => .bool false
  | a :: r => .or a (anyT r)

def allT : List Term → Term
  | [] => tt
  | a :: r => .and a (allT r)

/-- The slots with `x` in the first free one, after the pending flag `p` (whether `x` still waits for a slot); the
second result is whether it still waits after the last slot. -/
def insertSlots (x : List Term) : Term → List Slot → List Slot × Term
  | p, [] => ([], p)
  | p, (f, ys) :: S =>
    let here := Term.and p (.not f)
    let (S', p') := insertSlots x (.and p f) S
    ((.or f here, List.zipWith (fun a b => Term.ite here a b) x ys) :: S', p')

/-- The slots `T` with the items of each occupied slot of `S` in the first free slot in turn, shared after each
insertion; the second result is that each found one. -/
def moveAll (d dt w : Nat) : List Slot → List Slot → List Slot × Term
  | T, [] => (T, tt)
  | T, (f, xs) :: S =>
    let (T', p) := insertSlots xs f T
    let (T'', c) := moveAll d dt w (slotsOf d dt T'.length w (slotsTerm d dt T')) S
    (T'', .and (.not p) c)

/-- The slots `S` carried into `n` slots of the collection datatype `d`: padded with free slots holding `dflt` when
they fit, else moved one by one into `n` free slots, with the condition that the occupied ones fit. -/
def resizeSlots (d dt : Nat) (dflt : List Term) (n : Nat) (S : List Slot) : List Slot × Term :=
  if S.length ≤ n then (S ++ List.replicate (n - S.length) (.bool false, dflt), tt)
  else moveAll d dt dflt.length (List.replicate n (.bool false, dflt)) S

/-- The term `found xs` of the first occupied slot whose items satisfy `hit`, or `none`. -/
def firstT (hit : List Term → Term) (found : List Term → Term) (none : Term) : List Slot → Term
  | [] => none
  | (f, xs) :: S => .ite (.and f (hit xs)) (found xs) (firstT hit found none S)

/-! What slots denote: each slot's flag a Bool and its items values; the collection is the items of the occupied
ones. -/

/-- `R` relates the lists item by item. -/
def Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall2 R as bs
  | _, _ => False

/-- The item values of the occupied slots. -/
def occupied (sv : List (Bool × List Val)) : List (List Val) :=
  sv.filterMap fun (b, vs) => if b then some vs else none

/-- The slot terms denote these flags and items. -/
def SlotsDen (M : Model) : List Slot → List (Bool × List Val) → Prop
  | [], [] => True
  | (f, xs) :: S, (b, vs) :: sv => f.denote M = .bool b ∧ Term.denotes M xs = vs ∧ SlotsDen M S sv
  | _, _ => False

/-- A collection value with these slots. -/
def slotsVal (d dt : Nat) (sv : List (Bool × List Val)) : Val := .ctor d 0 (sv.map fun (b, vs) => .ctor dt 0 (.bool b :: vs))

section
variable {M : Model}

theorem denotes_eq_map (ts : List Term) : Term.denotes M ts = ts.map (Term.denote M) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Term.denotes, ih]

theorem sel_ctor {x : Term} {d k : Nat} {vs : List Val} (j : Nat) (h : x.denote M = .ctor d k vs) :
    (Term.sel d k j x).denote M = vs[j]?.getD default := by
  simp [Term.denote, h]

theorem slotsDen_length : {S : List Slot} → {sv : List (Bool × List Val)} → SlotsDen M S sv → S.length = sv.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by simp [slotsDen_length h]

/-- The slot term at index `m` of the collection `s`. -/
def slotAt (d dt w : Nat) (s : Term) (m : Nat) : Slot :=
  (.sel dt 0 0 (.sel d 0 m s), (List.range w).map fun j => .sel dt 0 (j + 1) (.sel d 0 m s))

theorem slotsOf_den (d dt w : Nat) (s : Term) (sv : List (Bool × List Val)) (hs : s.denote M = slotsVal d dt sv)
    (hw : ∀ p ∈ sv, p.2.length = w) : SlotsDen M (slotsOf d dt sv.length w s) sv := by
  have key : ∀ (s : Term) (hs : s.denote M = slotsVal d dt sv) (k : Nat) (rest : List (Bool × List Val)), (∀ p ∈ rest, p.2.length = w) →
      (∀ i (h : i < rest.length), (Term.sel d 0 (k + i) s).denote M = .ctor dt 0 (.bool rest[i].1 :: rest[i].2)) →
      SlotsDen M ((List.range rest.length).map fun i => slotAt d dt w s (k + i)) rest := by
    intro s _ k rest
    induction rest generalizing k with
    | nil => intro _ _; trivial
    | cons p rest ih =>
      intro hw' hi
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      have h0 : (Term.sel d 0 (k + 0) s).denote M = .ctor dt 0 (.bool p.1 :: p.2) := hi 0 (by simp)
      refine ⟨show (Term.sel dt 0 0 (Term.sel d 0 (k + 0) s)).denote M = _ by rw [sel_ctor 0 h0]; rfl, ?_, ?_⟩
      · show Term.denotes M ((List.range w).map fun j => Term.sel dt 0 (j + 1) (Term.sel d 0 (k + 0) s)) = _
        rw [denotes_eq_map, List.map_map]
        have hl := hw' p (by simp)
        apply List.ext_getElem (by simp [hl])
        intro j h1 h2
        simp only [List.getElem_map, List.getElem_range, Function.comp]
        rw [sel_ctor (j + 1) h0]
        simp [h2]
      · have e : ((fun i => slotAt d dt w s (k + i)) ∘ Nat.succ) = fun i => slotAt d dt w s (k + 1 + i) := by
          funext i; simp only [Function.comp]; congr 1; omega
        rw [e]
        exact ih (k + 1) (fun q hq => hw' q (by simp [hq])) (fun i h => by
          have := hi (i + 1) (by simp; omega)
          rw [show k + 1 + i = k + (i + 1) by omega]
          simpa using this)
  have := key s.share (by simp [hs]) 0 sv hw (fun i h => by simp [Term.denote, hs, slotsVal, h])
  simpa [slotsOf, slotAt] using this

theorem denotes_slots (dt : Nat) : {S : List Slot} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    Term.denotes M (S.map fun (f, xs) => Term.ctor dt 0 (f :: xs)) = sv.map fun (b, vs) => .ctor dt 0 (.bool b :: vs)
  | [], [], _ => rfl
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hx, h⟩ => by
    simp only [List.map_cons, Term.denotes, Term.denote, hf, hx, denotes_slots dt h]

theorem slotsTerm_den (d dt : Nat) {S : List Slot} {sv : List (Bool × List Val)} (h : SlotsDen M S sv) :
    (slotsTerm d dt S).denote M = slotsVal d dt sv := by
  simp only [slotsTerm, Term.denote_share, slotsVal, Term.denote, denotes_slots dt h]

/-- The number of occupied slots. -/
def sizeT (S : List Slot) : Term := sumT (S.map fun (f, _) => .ite f (.int 1) (.int 0))
def countT (S : List Slot) (qs : List Term) : Term :=
  sumT (List.zipWith (fun (f, _) q => .ite (.and f q) (.int 1) (.int 0)) S qs)
def anySlotT (S : List Slot) (qs : List Term) : Term := anyT (List.zipWith (fun (f, _) q => .and f q) S qs)
def allSlotT (S : List Slot) (qs : List Term) : Term := allT (List.zipWith (fun (f, _) q => .or (.not f) q) S qs)
def filterSlots (S : List Slot) (qs : List Term) : List Slot := List.zipWith (fun (f, xs) q => (.and f q, xs)) S qs

theorem sizeT_den : {S : List Slot} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    (sizeT S).denote M = .int (occupied sv).length
  | [], [], _ => rfl
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, _, h⟩ => by
    have := sizeT_den h
    simp only [sizeT, sumT, List.map_cons, Term.denote, hf, Val.toBool, Val.toInt] at this ⊢
    rw [this]; cases b
    · simp [occupied]
    · simp [occupied]; omega

/-- The slots denote `sv`; the occupied ones hold the items `ys` in order, related by `E`, and there each `q`, the
term of a function at the slot's item, denotes a value that `V` relates to the item. Every operation that applies a
function slot by slot rests on this relation. -/
def AlignedV {α : Type} (M : Model) (E : α → List Val → Prop) (V : α → Val → Prop) :
    List Slot → List Term → List (Bool × List Val) → List α → Prop
  | [], [], [], [] => True
  | (f, xs) :: S, _ :: qs, (false, vs) :: sv, ys =>
    f.denote M = .bool false ∧ Term.denotes M xs = vs ∧ AlignedV M E V S qs sv ys
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys =>
    f.denote M = .bool true ∧ Term.denotes M xs = vs ∧ E y vs ∧ V y (q.denote M) ∧ AlignedV M E V S qs sv ys
  | _, _, _, _ => False

/-- `AlignedV` for a predicate: each `q` denotes `P` of its item. -/
abbrev Aligned {α : Type} (M : Model) (E : α → List Val → Prop) (P : α → Bool) :=
  AlignedV M E (fun y v => v = .bool (P y))

/-- Occupied slots hold the items `ys` in order, related by `E`. -/
def Holds2 {α : Type} (E : α → List Val → Prop) (ys : List α) (sv : List (Bool × List Val)) : Prop :=
  Forall2 E ys (occupied sv)

section
variable {α : Type} {E : α → List Val → Prop} {P : α → Bool}

theorem countT_den : {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    Aligned M E P S qs sv ys → (countT S qs).denote M = .int (ys.filter P).length
  | [], [], [], [], _ => rfl
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, _, h⟩ => by
    have := countT_den h
    simp only [countT, sumT, List.zipWith_cons_cons, Term.denote, hf, Val.toBool, Val.toInt] at this ⊢
    rw [this]; simp
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys, ⟨hf, _, _, hq, h⟩ => by
    have := countT_den h
    simp only [countT, sumT, List.zipWith_cons_cons, Term.denote, hf, hq, Val.toBool, Val.toInt] at this ⊢
    rw [this]; cases hP : P y
    · simp [hP]
    · simp [hP]; omega

theorem anySlotT_den : {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    Aligned M E P S qs sv ys → (anySlotT S qs).denote M = .bool (ys.any P)
  | [], [], [], [], _ => rfl
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, _, h⟩ => by
    have := anySlotT_den h
    simp only [anySlotT, anyT, List.zipWith_cons_cons, Term.denote, hf, Val.toBool] at this ⊢
    rw [this]; simp
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys, ⟨hf, _, _, hq, h⟩ => by
    have := anySlotT_den h
    simp only [anySlotT, anyT, List.zipWith_cons_cons, Term.denote, hf, hq, Val.toBool] at this ⊢
    rw [this]; simp

theorem allSlotT_den : {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    Aligned M E P S qs sv ys → (allSlotT S qs).denote M = .bool (ys.all P)
  | [], [], [], [], _ => rfl
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, _, h⟩ => by
    have := allSlotT_den h
    simp only [allSlotT, allT, List.zipWith_cons_cons, Term.denote, hf, Val.toBool] at this ⊢
    rw [this]; simp
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys, ⟨hf, _, _, hq, h⟩ => by
    have := allSlotT_den h
    simp only [allSlotT, allT, List.zipWith_cons_cons, Term.denote, hf, hq, Val.toBool] at this ⊢
    rw [this]; simp

theorem filterSlots_den : {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    Aligned M E P S qs sv ys → ∃ sv', SlotsDen M (filterSlots S qs) sv' ∧ Holds2 E (ys.filter P) sv' ∧
      sv'.map (·.2) = sv.map (·.2)
  | [], [], [], [], _ => ⟨[], trivial, by simp [Holds2, occupied, Forall2], rfl⟩
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, hx, h⟩ => by
    obtain ⟨sv', h1, h2, h3⟩ := filterSlots_den h
    exact ⟨(false, vs) :: sv', ⟨by simp [Term.denote, hf, Val.toBool], hx, h1⟩, by simpa [Holds2, occupied] using h2,
      by simp [h3]⟩
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys, ⟨hf, hx, he, hq, h⟩ => by
    obtain ⟨sv', h1, h2, h3⟩ := filterSlots_den h
    refine ⟨(P y, vs) :: sv', ⟨by simp [Term.denote, hf, hq, Val.toBool], hx, h1⟩, ?_, by simp [h3]⟩
    cases hP : P y <;> simp only [Holds2, occupied, List.filter_cons, hP] at h2 ⊢
    · simpa using h2
    · simpa [Forall2] using ⟨he, h2⟩

end

/-- The guards of per-slot conditions: each must hold where its slot is occupied. -/
def guardsT (S : List Slot) (cs : List Term) : Term := allT (List.zipWith (fun (f, _) c => .or (.not f) c) S cs)

theorem guardsT_holds : {S : List Slot} → {cs : List Term} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    S.length = cs.length → ((guardsT S cs).denote M).toBool = true →
    ∀ i (h : i < sv.length), sv[i].1 = true → ∃ c, cs[i]? = some c ∧ (c.denote M).toBool = true
  | [], [], [], _, _, _, i, h, _ => nomatch h
  | (f, _) :: S, c :: cs, (b, _) :: sv, ⟨hf, _, h⟩, hl, hg, i, hi, hb => by
    simp only [guardsT, allT, List.zipWith_cons_cons, Term.denote, hf, Val.toBool, Bool.and_eq_true] at hg
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hb
      subst hb
      simp only [Bool.not_true, Bool.false_or] at hg
      exact ⟨c, rfl, hg.1⟩
    | succ i =>
      exact guardsT_holds h (by simpa using hl) hg.2 i (by simpa using hi) (by simpa using hb)

/-- What inserting `xv` into the slots `sv` gives, with whether it still waits for a slot. -/
def insertVals (xv : List Val) : Bool → List (Bool × List Val) → List (Bool × List Val) × Bool
  | p, [] => ([], p)
  | p, (b, vs) :: sv =>
    let here := p && !b
    let (sv', p') := insertVals xv (p && b) sv
    ((b || here, if here then xv else vs) :: sv', p')

theorem zip_ite (c : Term) (cb : Bool) (hc : c.denote M = .bool cb) : (x ys : List Term) → x.length = ys.length →
    Term.denotes M (List.zipWith (fun a b => Term.ite c a b) x ys) =
      if cb then Term.denotes M x else Term.denotes M ys
  | [], [], _ => by cases cb <;> rfl
  | a :: x, b :: ys, hl => by
    simp only [List.zipWith_cons_cons, Term.denotes, zip_ite c cb hc x ys (by simpa using hl)]
    simp only [Term.denote, hc, Val.toBool]
    cases cb <;> rfl

theorem insertSlots_den (x : List Term) (xv : List Val) (hx : Term.denotes M x = xv) :
    {S : List Slot} → {sv : List (Bool × List Val)} → (p : Term) → (pb : Bool) → p.denote M = .bool pb →
    SlotsDen M S sv → (∀ q ∈ sv, q.2.length = x.length) →
    SlotsDen M (insertSlots x p S).1 (insertVals xv pb sv).1 ∧
      (insertSlots x p S).2.denote M = .bool (insertVals xv pb sv).2
  | [], [], p, pb, hp, _, _ => ⟨trivial, hp⟩
  | (f, ys) :: S, (b, vs) :: sv, p, pb, hp, ⟨hf, hy, h⟩, hl => by
    have hpf : (Term.and p f).denote M = .bool (pb && b) := by simp [Term.denote, hp, hf, Val.toBool]
    obtain ⟨ih1, ih2⟩ := insertSlots_den x xv hx (pb := pb && b) (.and p f) hpf h (fun q hq => hl q (by simp [hq]))
    refine ⟨⟨?_, ?_, ih1⟩, ih2⟩
    · simp [Term.denote, hf, hp, Val.toBool]
    · have hlen : ys.length = x.length := by
        have := hl (b, vs) (by simp)
        rw [← hy, denotes_eq_map] at this; simpa using this
      have hhere : (Term.and p (.not f)).denote M = .bool (pb && !b) := by simp [Term.denote, hp, hf, Val.toBool]
      rw [zip_ite _ _ hhere x ys hlen.symm, hx, hy]

theorem insertVals_occupied (xv : List Val) : (pb : Bool) → (sv : List (Bool × List Val)) →
    (occupied (insertVals xv pb sv).1).Perm
      ((if (insertVals xv pb sv).2 = false ∧ pb = true then [xv] else []) ++ occupied sv) ∧
    (insertVals xv pb sv).2 = (pb && sv.all (·.1))
  | pb, [] => by cases pb <;> simp [insertVals, occupied]
  | pb, (b, vs) :: sv => by
    obtain ⟨ih, hp⟩ := insertVals_occupied xv (pb && b) sv
    simp only [insertVals]
    refine ⟨?_, by rw [hp]; cases pb <;> cases b <;> simp⟩
    cases pb <;> cases b
    · simpa [occupied] using ih
    · simpa [occupied] using ih.cons vs
    · have h0 : (insertVals xv false sv).2 = false := by simpa using hp
      simpa [occupied, h0] using ih.cons xv
    · simp only [Bool.and_self] at ih hp
      simp only [occupied, Bool.not_true, Bool.and_false, Bool.and_true,
        Bool.false_eq_true, ite_false, ite_true, List.filterMap_cons] at ih ⊢
      refine (ih.cons vs).trans ?_
      split
      · exact List.perm_middle.symm
      · exact List.Perm.refl _

theorem insertVals_length (xv : List Val) (w : Nat) (hx : xv.length = w) : (pb : Bool) →
    (sv : List (Bool × List Val)) → (∀ q ∈ sv, q.2.length = w) →
    (insertVals xv pb sv).1.length = sv.length ∧ ∀ q ∈ (insertVals xv pb sv).1, q.2.length = w
  | _, [], _ => ⟨rfl, by simp [insertVals]⟩
  | pb, (b, vs) :: sv, hl => by
    obtain ⟨h1, h2⟩ := insertVals_length xv w hx (pb && b) sv (fun q hq => hl q (by simp [hq]))
    simp only [insertVals, List.length_cons, h1, List.mem_cons, forall_eq_or_imp, true_and]
    refine ⟨?_, h2⟩
    split
    · exact hx
    · exact hl (b, vs) (by simp)

/-- The result of the first occupied slot whose hit holds, or `none`. -/
def pickT (none : Term) : List (Term × Term × Term) → Term
  | [] => none
  | (f, h, r) :: rest => .ite (.and f h) r (pickT none rest)

/-- Per slot: flag `b`, and where occupied, whether it hits and what it gives. -/
def PickDen (M : Model) : List (Term × Term × Term) → List (Bool × Bool × Val) → Prop
  | [], [] => True
  | (f, h, r) :: rest, (b, hb, rv) :: pv =>
    f.denote M = .bool b ∧ (b = true → h.denote M = .bool hb ∧ r.denote M = rv) ∧ PickDen M rest pv
  | _, _ => False

theorem pickT_den (none : Term) : {T : List (Term × Term × Term)} → {pv : List (Bool × Bool × Val)} →
    PickDen M T pv → (pickT none T).denote M =
      (((pv.filter fun (b, hb, _) => b && hb).head?.map (·.2.2)).getD (none.denote M))
  | [], [], _ => rfl
  | (f, h, r) :: rest, (b, hb, rv) :: pv, ⟨hf, hr, hrest⟩ => by
    simp only [pickT, Term.denote, hf, Val.toBool]
    cases b
    · simp [pickT_den none hrest]
    · obtain ⟨hh, hrv⟩ := hr rfl
      simp only [hh, Bool.true_and]
      cases hb
      · simp [pickT_den none hrest]
      · simp [hrv]

theorem mapM_ok {ε α β : Type} (g : α → Except ε β) : (xs : List α) → (ys : List β) → xs.mapM g = .ok ys →
    Forall2 (fun x y => g x = .ok y) xs ys
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; trivial
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : g x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM g with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok ys' =>
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact ⟨hx, mapM_ok g xs ys' hxs⟩

/-- Forall2 survives reordering the right list, with the left list reordered alike. -/
theorem forall2_perm {α β : Type} {R : α → β → Prop} {bs bs' : List β} (hp : bs.Perm bs') :
    ∀ {as : List α}, Forall2 R as bs → ∃ as', as'.Perm as ∧ Forall2 R as' bs' := by
  induction hp with
  | nil => intro as h; exact ⟨as, List.Perm.refl _, h⟩
  | cons b _ ih =>
    intro as h
    match as, h with
    | a :: as, ⟨hab, h⟩ =>
      obtain ⟨as', hp', h'⟩ := ih h
      exact ⟨a :: as', hp'.cons a, hab, h'⟩
  | swap b c l =>
    intro as h
    match as, h with
    | a1 :: a2 :: as, ⟨h1, h2, h⟩ => exact ⟨a2 :: a1 :: as, List.Perm.swap a1 a2 as, h2, h1, h⟩
  | trans _ _ ih1 ih2 =>
    intro as h
    obtain ⟨as1, hp1, h1⟩ := ih1 h
    obtain ⟨as2, hp2, h2⟩ := ih2 h1
    exact ⟨as2, hp2.trans hp1, h2⟩

theorem aligned_of {α : Type} {E : α → List Val → Prop} {V : α → Val → Prop} (G : Slot → Term × Term → Prop)
    (hG : ∀ sl r y, G sl r → E y (Term.denotes M sl.2) → (r.2.denote M).toBool = true → V y (r.1.denote M)) :
    {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List α} → {R : List (Term × Term)} →
    SlotsDen M S sv → Holds2 E ys sv → Forall2 G S R → ((guardsT S (R.map (·.2))).denote M).toBool = true →
    AlignedV M E V S (R.map (·.1)) sv ys
  | [], [], [], [], _, _, _, _ => trivial
  | [], [], _ :: _, [], _, h, _, _ => nomatch h
  | (f, xs) :: S, (false, vs) :: sv, ys, r :: R, ⟨hf, hx, h⟩, he, ⟨_, hR⟩, hg => by
    simp only [guardsT, allT, List.map_cons, List.zipWith_cons_cons, Term.denote, hf, Val.toBool,
      Bool.and_eq_true] at hg
    exact ⟨hf, hx, aligned_of G hG h (by simpa [Holds2, occupied] using he) hR hg.2⟩
  | (f, xs) :: S, (true, vs) :: sv, y :: ys, r :: R, ⟨hf, hx, h⟩, he, ⟨hr, hR⟩, hg => by
    simp only [guardsT, allT, List.map_cons, List.zipWith_cons_cons, Term.denote, hf, Val.toBool,
      Bool.and_eq_true, Bool.not_true, Bool.false_or] at hg
    simp only [Holds2, occupied, ite_true, List.filterMap_cons, Forall2] at he
    exact ⟨hf, hx, he.1, hG _ r y hr (by rw [hx]; exact he.1) hg.1,
      aligned_of G hG h he.2 hR hg.2⟩
  | (_, _) :: _, (true, _) :: _, [], _, _, he, _, _ => by
    simp [Holds2, occupied, Forall2] at he

theorem holds2_length {α : Type} {E : α → List Val → Prop} {ys : List α} {sv : List (Bool × List Val)}
    (h : Holds2 E ys sv) : ys.length = (occupied sv).length := by
  unfold Holds2 at h
  generalize occupied sv = os at h
  induction ys generalizing os with
  | nil => cases os <;> simp_all [Forall2]
  | cons y ys ih => cases os with
    | nil => simp [Forall2] at h
    | cons o os => simp [ih os h.2]

theorem aligned_map {α : Type} {E : α → List Val → Prop} {V : α → Val → Prop} (Q : List Term → Term)
    (hQ : ∀ y xs, E y (Term.denotes M xs) → V y ((Q xs).denote M)) :
    {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List α} → SlotsDen M S sv → Holds2 E ys sv →
    AlignedV M E V S (S.map fun sl => Q sl.2) sv ys
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h => nomatch h
  | (f, xs) :: S, (false, vs) :: sv, ys, ⟨hf, hx, h⟩, he =>
    ⟨hf, hx, aligned_map Q hQ h (by simpa [Holds2, occupied] using he)⟩
  | (f, xs) :: S, (true, vs) :: sv, y :: ys, ⟨hf, hx, h⟩, he => by
    simp only [Holds2, occupied, ite_true, List.filterMap_cons, Forall2] at he
    exact ⟨hf, hx, he.1, hQ y xs (by rw [hx]; exact he.1), aligned_map Q hQ h he.2⟩
  | (_, _) :: _, (true, _) :: _, [], _, he => by simp [Holds2, occupied, Forall2] at he

theorem alignedV_mono {α : Type} {E : α → List Val → Prop} {V V' : α → Val → Prop} (h : ∀ y v, V y v → V' y v) :
    {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    AlignedV M E V S qs sv ys → AlignedV M E V' S qs sv ys
  | [], [], [], [], _ => trivial
  | (_, _) :: _, _ :: _, (false, _) :: _, _, ⟨hf, hx, ha⟩ => ⟨hf, hx, alignedV_mono h ha⟩
  | (_, _) :: _, _ :: _, (true, _) :: _, _ :: _, ⟨hf, hx, he, hq, ha⟩ => ⟨hf, hx, he, h _ _ hq, alignedV_mono h ha⟩

/-- The sum of the Int terms of the occupied slots. -/
def sumSlotT (S : List Slot) (qs : List Term) : Term := sumT (List.zipWith (fun (f, _) q => .ite f q (.int 0)) S qs)

theorem sumSlotT_den {α : Type} {E : α → List Val → Prop} {g : α → Int} :
    {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    AlignedV M E (fun y v => v = .int (g y)) S qs sv ys → (sumSlotT S qs).denote M = .int (ys.map g).sum
  | [], [], [], [], _ => rfl
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, _, h⟩ => by
    have := sumSlotT_den h
    simp only [sumSlotT, sumT, List.zipWith_cons_cons, Term.denote, hf, Val.toBool, Val.toInt] at this ⊢
    rw [this]; simp
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys, ⟨hf, _, _, hq, h⟩ => by
    have := sumSlotT_den h
    simp only [sumSlotT, sumT, List.zipWith_cons_cons, Term.denote, hf, hq, Val.toBool, Val.toInt] at this ⊢
    rw [this]; simp

/-- The slots with each one's items replaced by `N` of its items and its term in `qs`; flags stay. -/
def mapSlots (N : List Term → Term → List Term) (S : List Slot) (qs : List Term) : List Slot :=
  List.zipWith (fun (f, xs) q => (f, N xs q)) S qs

theorem mapSlots_den {α β : Type} {E : α → List Val → Prop} {V : α → Val → Prop} {E' : β → List Val → Prop}
    (g : α → β) (N : List Term → Term → List Term) (w : Nat)
    (hN : ∀ y xs q, E y (Term.denotes M xs) → V y (q.denote M) → E' (g y) (Term.denotes M (N xs q)))
    (hw : ∀ xs q, (N xs q).length = w) :
    {S : List Slot} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    AlignedV M E V S qs sv ys → ∃ sv', SlotsDen M (mapSlots N S qs) sv' ∧ sv'.length = sv.length ∧
      (∀ p ∈ sv', p.2.length = w) ∧ Holds2 E' (ys.map g) sv'
  | [], [], [], [], _ => ⟨[], trivial, rfl, by simp, by simp [Holds2, occupied, Forall2]⟩
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, _, h⟩ => by
    obtain ⟨sv', h1, h2, h3, h4⟩ := mapSlots_den g N w hN hw h
    refine ⟨(false, Term.denotes M (N xs q)) :: sv', ⟨hf, rfl, h1⟩, by simp [h2], ?_, by simpa [Holds2, occupied] using h4⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by rw [denotes_eq_map, List.length_map, hw], h3⟩
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y :: ys, ⟨hf, hx, he, hq, h⟩ => by
    obtain ⟨sv', h1, h2, h3, h4⟩ := mapSlots_den g N w hN hw h
    refine ⟨(true, Term.denotes M (N xs q)) :: sv', ⟨hf, rfl, h1⟩, by simp [h2], ?_, ?_⟩
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨by rw [denotes_eq_map, List.length_map, hw], h3⟩
    · simp only [Holds2, occupied, ite_true, List.filterMap_cons, List.map_cons, Forall2] at h4 ⊢
      exact ⟨hN y xs q (hx ▸ he) hq, h4⟩

theorem slotsDen_append : {S : List Slot} → {sv : List (Bool × List Val)} → {T : List Slot} →
    {tv : List (Bool × List Val)} → SlotsDen M S sv → SlotsDen M T tv → SlotsDen M (S ++ T) (sv ++ tv)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ⟨hf, hx, h⟩, h' => ⟨hf, hx, slotsDen_append h h'⟩

theorem occupied_append (sv tv : List (Bool × List Val)) : occupied (sv ++ tv) = occupied sv ++ occupied tv := by
  simp [occupied, List.filterMap_append]

/-- With nothing pending, inserting changes no slot. -/
theorem insertVals_false (xv : List Val) : (sv : List (Bool × List Val)) → insertVals xv false sv = (sv, false)
  | [] => rfl
  | (b, vs) :: sv => by simp [insertVals, insertVals_false xv sv]

theorem empty_den (xs : List Term) : (n : Nat) →
    SlotsDen M (List.replicate n (Term.bool false, xs)) (List.replicate n (false, Term.denotes M xs))
  | 0 => trivial
  | n + 1 => ⟨rfl, rfl, empty_den xs n⟩

theorem occupied_empty (vs : List Val) (n : Nat) : occupied (List.replicate n (false, vs)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, occupied]

end

end Tazuna.Smt
