import Tazuna.Smt.AnswerStep

/-! The bounds a script checks within. `create(table:, at_most:)` bounds the records in one table of the records at any
time, so a table type gets as many slots as the largest `at_most` among the creates of that type (`boundSlots`): every
table a create bounds fits, and one sort serves every table of the type, which the type-generic built-in encodings
need. Where creates of one type differ, the smaller ones are terms: `createsT` says, of a records term, that each
create's table has at most `at_most` occupied slots. `createsT_iff` proves the term exact: in every model where the
codes' condition holds it holds exactly when the records it denotes are within every create (`within`). So a script
asserts it of the state before a step, and its negation of the state after one is the bound-reached condition
(`boundReachedT`): a model of it is a step that leaves the bounds, which prove reports as `Undecided.boundReached`. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {r : Ty}

/-- Whether a create bounds tables of type `t`. -/
def _root_.Tazuna.Ir.CreateV.bounds (c : CreateV r) (t : Ty) : Bool := (Ty.same (.table c.key c.value) t).isSome

/-- The slots of each bag and table type: a table type the largest `at_most` among its creates, and a bag, or a table
no create bounds, `items`. Lists get theirs from their literals (`listSlots`). -/
def boundSlots (b : BoundsV r) : Ty → Nat
  | .table k v => match b.creates.filter (·.bounds (.table k v)) with
    | [] => b.items.toNat
    | cs => cs.foldl (fun m c => max m c.atMost.toNat) 0
  | .bag _ => b.items.toNat
  | _ => 0

/-- The records are within every create: each one's table holds at most `at_most` records. -/
def within (cs : List (CreateV r)) (x : r.den0) : Bool :=
  cs.all fun c => decide (((c.table.fn (x, ())).1.length : Int) ≤ c.atMost)

end

theorem foldl_max_ge {α : Type} (g : α → Nat) : (xs : List α) → (m : Nat) →
    m ≤ xs.foldl (fun m c => max m (g c)) m ∧ ∀ c ∈ xs, g c ≤ xs.foldl (fun m c => max m (g c)) m
  | [], m => ⟨Nat.le_refl m, by simp⟩
  | c :: xs, m => by
    obtain ⟨h1, h2⟩ := foldl_max_ge g xs (max m (g c))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, ?_⟩
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 c' hc'

/-- Every table a create bounds fits its type's slots. -/
theorem atMost_le_slots {r : Ty} (b : BoundsV r) (c : CreateV r) (hc : c ∈ b.creates) :
    c.atMost.toNat ≤ boundSlots b (.table c.key c.value) := by
  have hm : c ∈ b.creates.filter (·.bounds (.table c.key c.value)) :=
    List.mem_filter.2 ⟨hc, by simp [CreateV.bounds, Ty_same_self]⟩
  simp only [boundSlots]
  split
  · rename_i h; rw [h] at hm; nomatch hm
  · exact (foldl_max_ge (fun c : CreateV r => c.atMost.toNat) _ 0).2 c hm

section
variable (L : Layout) {r : Ty}

/-- One create's limit at the records term `records`, with its condition. -/
def createT (c : CreateV r) (records : Term) : Except Refusal (Term × Term) := do
  let (f, c1) ← c.table.code L
  let rc ← need "records that have no term" (Code.ofTerm? r records)
  let (t, c2) ← f (rc, ())
  let (d, n, dt) ← collD L (.table c.key c.value) [c.key, c.value]
  pure (.le (sizeT (slotsOf d dt n 2 t)) (.int c.atMost), andT c1 c2)

/-- Every create's limit at the records term, with the codes' condition. -/
def createsT (records : Term) : List (CreateV r) → Except Refusal (Term × Term)
  | [] => pure (tt, tt)
  | c :: cs => do
    let (l, k) ← createT L c records
    let (ls, ks) ← createsT records cs
    pure (.and l ls, andT k ks)

/-- The bound-reached condition of a step whose condition is `cond` and whose records after are `records`: the
step outgrew a collection's slots, or its records leave a create's bound. -/
def boundReachedT (cs : List (CreateV r)) (cond records : Term) : Except Refusal (Term × Term) := do
  let (l, k) ← createsT L records cs
  pure (.or (.not cond) (.not l), k)

end

theorem cast_table_length (K K' V V' : Sem) (hk : K = K') (hv : V = V') (e : (Sem.table K V).1 = (Sem.table K' V').1)
    (x : (Sem.table K V).1) : (cast e x).1.length = x.1.length := by
  subst hk; subst hv; rfl

/-- Reading a table at the structure level keeps its records. -/
theorem Ty.up_table_length (k w : Ty) (h : (Ty.table k w).isData = true) (x : (Ty.table k w).den0) :
    (Ty.up (.table k w) h x).1.length = x.1.length := by
  simp only [Ty.isData, Bool.and_eq_true] at h
  exact cast_table_length _ _ _ _ (Ty.semWith_data Dsl.val_fresh k h.1).symm
    (Ty.semWith_data Dsl.val_fresh w h.2).symm _ x

section
variable {M : Model} {L : Layout} {r : Ty}

theorem createT_iff (hr : r.isData = true) (c : CreateV r) {records l k : Term} (x : r.den0)
    (hx : RelV L r (Ty.up r hr x) (records.denote M)) (h : createT L c records = .ok (l, k)) (hk : Holds M k) :
    Holds M l ↔ ((c.table.fn (x, ())).1.length : Int) ≤ c.atMost := by
  obtain ⟨⟨f, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨rc, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨t, c2⟩, h3, h⟩ := bind_ok.1 h
  obtain ⟨⟨d, n, dt⟩, h4, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  rw [holds_andT] at hk
  have ht := c.table.ht
  have hkw : (Ty.table c.key c.value).isData = true := by simp only [Ty.isData, Bool.and_eq_true] at ht ⊢; exact ht.2
  have hargs1 : (Ty.tuple [r]).isData = true := by simp [Ty.isData, Ty.isDatas, hr]
  have hf := c.table.code_fn ht h1 hk.1
  have hrc : Smt.Rel M L r (Ty.up r hr x) rc := (rel_ofTerm (need_ok.1 h2) _).2 hx
  have hargs : Smt.Rels M L [r] (Ty.up (.tuple [r]) hargs1 (x, ())) (rc, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [r]) hargs1 (x, ())).1 rc ∧ True
    erw [Ty.up_tuple _ _ _ hr rfl]; exact ⟨hrc, trivial⟩
  have htab := hf _ _ hargs t c2 h3 hk.2
  erw [Ty.up_fn _ _ _ hargs1 hkw] at htab
  obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view htab h4
  have hsize := sizeT_den hS
  rw [← holds2_length hh, hperm.length_eq, Ty.up_table_length _ _ hkw] at hsize
  simp [Holds, Term.denote, hsize, Val.toBool, Val.toInt]

/-- The limits are exact: wherever the codes' condition holds, they hold exactly when the records the term denotes
are within every create. -/
theorem createsT_iff (hr : r.isData = true) {records : Term} (x : r.den0)
    (hx : RelV L r (Ty.up r hr x) (records.denote M)) :
    (cs : List (CreateV r)) → {l k : Term} → createsT L records cs = .ok (l, k) → Holds M k →
      (Holds M l ↔ within cs x = true)
  | [], _, _, h, _ => by
    cases pure_ok.1 h; simp [Holds, tt, Term.denote, Val.toBool, within]
  | c :: cs, _, _, h, hk => by
    obtain ⟨⟨l1, k1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨ls, ks⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_andT] at hk
    have e1 := createT_iff hr c x hx h1 hk.1
    have e2 := createsT_iff hr x hx cs h2 hk.2
    simp only [within, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at e2 ⊢
    rw [← e1, ← e2]
    simp [Holds, Term.denote, Val.toBool]

/-- The bound-reached condition is exact: where the step's condition holds, it holds exactly when the records after
leave a create's bound; where it does not, it holds. -/
theorem boundReached_iff (hr : r.isData = true) (cs : List (CreateV r)) {cond records b k : Term}
    (h : boundReachedT L cs cond records = .ok (b, k)) (hk : Holds M k) :
    (¬ Holds M cond → Holds M b) ∧
      (Holds M cond → ∀ x : r.den0, RelV L r (Ty.up r hr x) (records.denote M) → (Holds M b ↔ within cs x = false)) := by
  obtain ⟨⟨l, k'⟩, h1, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hb : Holds M (.or (.not cond) (.not l)) ↔ ¬ Holds M cond ∨ ¬ Holds M l := by
    simp [Holds, Term.denote, Val.toBool]
  refine ⟨fun hc => hb.2 (.inl hc), fun hc x hx => ?_⟩
  rw [hb, createsT_iff hr x hx cs h1 hk]
  simp [hc]

end

end Tazuna.Smt
