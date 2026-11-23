import Tazuna.Smt.Encode
import Tazuna.Thm.Guarantee

/-!
The encoding of IR expressions agrees with Ir.eval (`seval_agrees`): under every model, an expression that `seval`
encodes throws exactly when its throw term holds, and else evaluates to the value that its symbolic value is. This is the
link from the SMT answers to the semantics, as Cedar's symbolic compiler proves of its encoding.
-/

namespace Tazuna.Thm.Smt.Encode

open Tazuna.Smt Tazuna.Ir Tazuna.Data Tazuna.Service

/-- The value and final state of an evaluation that starts in state `s`. -/
def run {α : Type} (x : EvalM α) (s : Trace) : Except Issue α × Trace := (ExceptT.run x).run s

theorem run_bind {α β : Type} (x : EvalM α) (f : α → EvalM β) (s : Trace) :
    run (x >>= f) s = (match run x s with
      | (.ok a, s') => run (f a) s'
      | (.error e, s') => (.error e, s')) := by
  simp only [run, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, StateT.run]
  rcases x s with ⟨r, s'⟩
  cases r <;> rfl

theorem run_pure {α : Type} (a : α) (s : Trace) : run (pure a : EvalM α) s = (.ok a, s) := rfl

theorem run_thrown {α : Type} (s : Trace) : run (thrown : EvalM α) s = (.error (.thrown none), s) := rfl

theorem run_note (p : RecordPart) (s : Trace) : (run (note p) s).1 = .ok () := by
  simp only [run, note, modify, modifyGet, MonadStateOf.modifyGet, ExceptT.run, ExceptT.lift, ExceptT.mk,
    monadLift, MonadLift.monadLift, StateT.run]
  rfl

/--
That `r` is what the evaluation result `x` is under `M`: `x` throws exactly when the throw term of `r` holds, and is
otherwise the value of `r`.
-/
def Agrees (M : Model) (recs : Records) (r : SRes) (x : Except Issue Val) : Prop :=
  match x with
  | .ok v => r.2.holds M = false ∧ v = r.1.conc M recs
  | .error _ => r.2.holds M = true

theorem holds_or (M : Model) (a b : Term) : (Term.or a b).holds M = (a.holds M || b.holds M) := rfl
theorem holds_and (M : Model) (a b : Term) : (Term.and a b).holds M = (a.holds M && b.holds M) := rfl
theorem holds_not (M : Model) (a : Term) : (Term.not a).holds M = !a.holds M := rfl
theorem holds_ite (M : Model) (c a b : Term) :
    (Term.ite c a b).holds M = if c.holds M then a.holds M else b.holds M := by
  simp only [Term.holds, Term.denote]; split <;> rfl
theorem holds_tt (M : Model) : tt.holds M = true := rfl
theorem holds_ff (M : Model) : ff.holds M = false := rfl

theorem conc_ite (M : Model) (recs : Records) (c : Term) (a b : SVal) :
    (SVal.ite c a b).conc M recs = if c.holds M then a.conc M recs else b.conc M recs := by
  simp [SVal.conc]

theorem conc_scalar (M : Model) (recs : Records) (t : Term) :
    (SVal.scalar t).conc M recs = (t.denote M).toScalar.toVal := by simp [SVal.conc]


theorem conc_mkBool (M : Model) (recs : Records) (t : Term) :
    (SVal.scalar (.mkBool t)).conc M recs = .json (.bool (t.holds M)) := rfl

theorem conc_mkInt (M : Model) (recs : Records) (t : Term) :
    (SVal.scalar (.mkInt t)).conc M recs = .json (.num ⟨(t.denote M).toInt, 0⟩) := rfl

theorem conc_undef (M : Model) (recs : Records) : (SVal.scalar undefT).conc M recs = .undef := rfl

/-- A value that no scalar is: what the conc of a symbolic value that is no scalar gives. -/
def NonScalar : Val → Prop
  | .json (.obj _) | .row .. | .table .. | .obj _ | .list _ | .emit .. => True
  | _ => False

theorem decide_int_eq_zero (n : Int) : decide (n = 0) = !n != 0 := by
  cases h : (n == 0) <;> simp_all [bne]

theorem decide_str_eq_empty (s : String) : decide (s = "") = s.isEmpty := by
  cases h : s.isEmpty
  · have : s ≠ "" := fun e => by simp [e] at h
    simp [this]
  · simp [String.isEmpty_iff.mp h]

theorem truthyT_holds (M : Model) (t : Term) : (truthyT t).holds M = truthy (t.denote M).toScalar.toVal := by
  cases h : (t.denote M).toScalar <;>
    simp [truthyT, Term.holds, Term.denote, h, Lit.toBool, intLit, strLit, Scalar.toVal,
      Scalar.toValue?, Val.ofOption, truthy, decide_int_eq_zero, decide_str_eq_empty]


theorem truthy_conc (M : Model) (recs : Records) : ∀ v : SVal, v.truthy.holds M = truthy (v.conc M recs)
  | .scalar t => by simp [SVal.truthy, SVal.conc, truthyT_holds]
  | .ite c a b => by
    rw [SVal.truthy, holds_ite, conc_ite, truthy_conc M recs a, truthy_conc M recs b]
    split <;> rfl
  | .json _ | .row .. | .single _ | .table _ | .obj _ | .list _ | .emit .. => rfl

/-- Whether a value is `undefined` or null, which `??` and `?.` test. -/
def isNullish : Val → Bool
  | .undef | .json .null => true
  | _ => false

theorem nullish_conc (M : Model) (recs : Records) : ∀ v : SVal, v.nullish.holds M = isNullish (v.conc M recs)
  | .scalar t => by
    cases h : (t.denote M).toScalar <;>
      simp [SVal.nullish, SVal.conc, nullishT, Term.holds, Term.denote, h, Lit.toBool, Scalar.toVal, Scalar.toValue?,
        Val.ofOption, isNullish]
  | .ite c a b => by
    rw [SVal.nullish, holds_ite, conc_ite, nullish_conc M recs a, nullish_conc M recs b]
    split <;> rfl
  | .json _ | .row .. | .single _ | .table _ | .obj _ | .list _ | .emit .. => rfl

theorem sameT_holds (M : Model) (a b : Term) :
    (sameT a b).holds M = same (a.denote M).toScalar.toVal (b.denote M).toScalar.toVal := by
  cases ha : (a.denote M).toScalar <;> cases hb : (b.denote M).toScalar <;>
    simp [sameT, Term.holds, Term.denote, ha, hb, Lit.toBool, Scalar.toVal, Scalar.toValue?, Val.ofOption, same]
  all_goals (rename_i x y; cases h : x == y <;> simp_all)

theorem same_json_left (fs : List (String × Value)) (w : Val) : same (.json (.obj fs)) w = false := by
  cases w with
  | json v => cases v <;> rfl
  | _ => rfl

theorem same_json_right (v : Val) (fs : List (String × Value)) : same v (.json (.obj fs)) = false := by
  cases v with
  | json v => cases v <;> rfl
  | _ => rfl

theorem same_conc (M : Model) (recs : Records) :
    ∀ a b : SVal, (a.same b).holds M = same (a.conc M recs) (b.conc M recs)
  | .ite c a b, w => by
    rw [SVal.same, holds_ite, conc_ite, same_conc M recs a w, same_conc M recs b w]
    split <;> rfl
  | .scalar t, .ite c x y => by
    rw [SVal.same, holds_ite, conc_ite, same_conc M recs (.scalar t) x, same_conc M recs (.scalar t) y]
    split <;> rfl
  | .scalar a, .scalar b => by simp [SVal.same, SVal.conc, sameT_holds]
  | .scalar _, .json _ => by simp [SVal.same, SVal.conc, same_json_right, holds_ff]
  | .scalar t, .row .. | .scalar t, .single _ | .scalar t, .table _ | .scalar t, .obj _ | .scalar t, .list _
  | .scalar t, .emit .. => by
    simp only [SVal.same, holds_ff, SVal.conc]
    cases (t.denote M).toScalar <;> rfl
  | .json _, w => by
    cases w <;> simp [SVal.same, SVal.conc, same_json_left, holds_ff]
  | .row .., w | .single _, w | .table _, w | .obj _, w | .list _, w | .emit .., w => by
    cases w <;> simp [SVal.same, SVal.conc, same, holds_ff]

theorem scalarOf_conc (M : Model) (recs : Records) : ∀ v : SVal,
    (v.scalarOf.2.holds M = false → v.conc M recs = (SVal.scalar v.scalarOf.1).conc M recs) ∧
      (v.scalarOf.2.holds M = true → NonScalar (v.conc M recs))
  | .scalar t => by simp [SVal.scalarOf, holds_ff]
  | .ite c a b => by
    have ha := scalarOf_conc M recs a
    have hb := scalarOf_conc M recs b
    simp only [SVal.scalarOf, holds_ite, conc_ite, conc_scalar, Term.denote]
    constructor
    · intro h
      split at h <;> rename_i hc <;> simp only [Term.holds] at hc <;> simp only [hc, ite_true] <;>
        simp_all [conc_scalar]
    · intro h
      split at h <;> rename_i hc <;> simp only [hc, ite_true] <;> simp_all
  | .json _ | .row .. | .single _ | .table _ | .obj _ | .list _ | .emit .. => by
    simp [SVal.scalarOf, holds_tt, SVal.conc, NonScalar]


theorem toVal_toValue? (v : Scalar) : v.toVal = Val.ofOption v.toValue? := rfl

theorem jsonField_conc (M : Model) (name : String) : ∀ fs : List (String × Term),
    ((jsonField name fs).denote M).toScalar.toValue? = (Value.obj (present M fs)).field? name
  | [] => by simp [jsonField, undefT, Term.denote, Lit.toScalar, Scalar.toValue?, present, Value.field?]
  | (n, t) :: fs => by
    have ih := jsonField_conc M name fs
    simp only [Value.field?, present, List.filterMap_cons] at ih ⊢
    by_cases hn : n = name
    · subst hn
      cases h : (t.denote M).toScalar <;>
        simp_all [jsonField, Term.denote, Lit.toBool, Scalar.toValue?]
    · have : (n == name) = false := by simp [hn]
      cases h : (t.denote M).toScalar <;> simp_all [jsonField, Scalar.toValue?]

theorem mkStr_eq_holds (M : Model) (a b : Term) :
    (Term.eq (.mkStr a) (.mkStr b)).holds M = decide ((a.denote M).toStr = (b.denote M).toStr) := by
  simp [Term.holds, Term.denote, Lit.toBool]

/-- The rows of the live slots of `ss`, as entity `e`'s. -/
def liveRows (M : Model) (e : String) (ss : List Slot) : Records := (ss.filter (·.live.holds M)).map (Slot.row M e)

theorem denote_ite (M : Model) (c a b : Term) :
    (Term.ite c a b).denote M = if c.holds M then a.denote M else b.denote M := rfl

theorem rowField_conc (M : Model) (e name : String) (k : Term) : ∀ ss : List Slot,
    ((rowField k name ss).denote M).toScalar.toVal =
      Val.ofOption (((liveRows M e ss).find? fun r => r.entity == e && r.key == some (k.denote M).toStr).bind
        (·.value.field? name))
  | [] => by simp [rowField, liveRows, undefT, Term.denote, Lit.toScalar, Scalar.toVal, Scalar.toValue?]
  | s :: ss => by
    have ih := rowField_conc M e name k ss
    rw [rowField, denote_ite]
    by_cases hl : s.live.holds M
    · by_cases hk : (s.key.denote M).toStr = (k.denote M).toStr
      · have hc : (Term.and s.live (.eq (.mkStr s.key) (.mkStr k))).holds M = true := by
          simp [holds_and, hl, mkStr_eq_holds, hk]
        rw [hc]; simp only [↓reduceIte]
        simp [liveRows, hl, Slot.row, hk, toVal_toValue?, jsonField_conc]
      · have hc : (Term.and s.live (.eq (.mkStr s.key) (.mkStr k))).holds M = false := by
          simp [holds_and, hl, mkStr_eq_holds, hk]
        rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [ih]
        simp [liveRows, hl, Slot.row, hk]
    · have hc : (Term.and s.live (.eq (.mkStr s.key) (.mkStr k))).holds M = false := by
        simp [holds_and, hl]
      rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [ih]
      simp [liveRows, hl]

theorem liveRows_append (M : Model) (e : String) (a b : List Slot) :
    liveRows M e (a ++ b) = liveRows M e a ++ liveRows M e b := by
  simp [liveRows, List.filter_append]

theorem find?_flatMap_none {α β : Type} (p : β → Bool) (f : α → List β) :
    ∀ xs : List α, (∀ x ∈ xs, ∀ y ∈ f x, p y = false) → (xs.flatMap f).find? p = none
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatMap_cons, List.find?_append, find?_flatMap_none p f xs (fun x' hx => h x' (by simp [hx]))]
    rw [List.find?_eq_none.mpr (fun y hy => by simp [h x (by simp) y hy])]
    rfl

/-- The rows of `r`'s keyed entities. -/
def keyedRows (M : Model) (r : SRecords) : Records := r.keyed.flatMap fun (e, slots) => liveRows M e slots

theorem keyedRows_find (M : Model) (e : String) (p : Row → Bool) (hp : ∀ row, p row = true → row.entity = e) :
    ∀ keyed : List (String × List Slot),
      ((keyed.flatMap fun (e', slots) => liveRows M e' slots).find? p) =
        (liveRows M e ((keyed.filter (·.1 == e)).flatMap (·.2))).find? p
  | [] => rfl
  | (e', slots) :: keyed => by
    have ih := keyedRows_find M e p hp keyed
    simp only [List.flatMap_cons, List.find?_append, List.filter_cons]
    by_cases he : e' = e
    · subst he
      rw [ih]
      simp only [beq_self_eq_true, ite_true, List.flatMap_cons, liveRows_append, List.find?_append]
    · have none : (liveRows M e' slots).find? p = none := by
        apply List.find?_eq_none.mpr
        intro row hrow hpr
        have := hp row hpr
        simp only [liveRows, List.mem_map] at hrow
        obtain ⟨s, _, rfl⟩ := hrow
        exact he (by simpa [Slot.row] using this)
      have : (e' == e) = false := by simp [he]
      simp [none, ih, this]

theorem conc_find_keyed (M : Model) (r : SRecords) (e : String) (key : String) :
    (r.conc M).find? (fun row => row.entity == e && row.key == some key) =
      (liveRows M e (r.slotsOf e)).find? (fun row => row.entity == e && row.key == some key) := by
  simp only [SRecords.conc, List.find?_append]
  have hs : (r.singles.map fun (e, fields) => ({ entity := e, key := none, value := .obj (present M fields) } : Row)).find?
      (fun row => row.entity == e && row.key == some key) = none := by
    apply List.find?_eq_none.mpr
    intro row hrow
    simp only [List.mem_map] at hrow
    obtain ⟨_, _, rfl⟩ := hrow
    simp
  rw [hs, Option.or_none]
  have := keyedRows_find M e (fun row => row.entity == e && row.key == some key)
    (fun row h => by simpa using (Bool.and_eq_true_iff.mp h).1) r.keyed
  simpa [liveRows, SRecords.slotsOf] using this


theorem conc_find_single (M : Model) (r : SRecords) (e : String) :
    (r.conc M).find? (fun row => row.entity == e && row.key == none) =
      (r.singles.lookup e).map fun fields => { entity := e, key := none, value := .obj (present M fields) } := by
  simp only [SRecords.conc, List.find?_append]
  rw [find?_flatMap_none _ _ _ (fun x _ row hrow => by
    simp only [List.mem_map] at hrow
    obtain ⟨_, _, rfl⟩ := hrow
    simp [Slot.row]), Option.none_or]
  induction r.singles with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨e', fields⟩ := p
    by_cases he : e' = e
    · subst he; simp
    · have : (e == e') = false := by simp [Ne.symm he]
      have hp : ((e' == e) && ((none : Option String) == none)) = false := by simp [he]
      rw [List.map_cons, List.find?_cons, List.lookup_cons, this]
      simp only [hp]
      exact ih

theorem run_note_pure {α : Type} (p : RecordPart) (x : α) (s : Trace) :
    (run (do note p; pure x : EvalM α) s).1 = .ok x := by
  rw [run_bind]
  rcases h : run (note p) s with ⟨r, s'⟩
  have := run_note p s
  rw [h] at this
  subst this
  rfl

theorem concFields_lookup (M : Model) (recs : Records) (name : String) : ∀ fs : List (String × SVal),
    (SVal.concFields M recs fs).lookup name = (fs.lookup name).map (·.conc M recs)
  | [] => rfl
  | (n, v) :: fs => by
    simp only [SVal.concFields, List.lookup_cons]
    split <;> simp [concFields_lookup M recs name fs]

theorem field_conc (M : Model) (r : SRecords) (name : String) (s : Trace) : ∀ v : SVal,
    isNullish (v.conc M (r.conc M)) = false →
      (run (fieldOf (v.conc M (r.conc M)) name) s).1 = .ok ((v.field r name).conc M (r.conc M))
  | .scalar t, h => by
    simp only [SVal.conc] at h ⊢
    cases hs : (t.denote M).toScalar <;>
      simp_all [Scalar.toVal, Scalar.toValue?, Val.ofOption, isNullish, fieldOf, run_pure, Value.field?, SVal.field,
        conc_undef]
  | .json fs, _ => by
    simp [SVal.conc, fieldOf, run_pure, SVal.field, toVal_toValue?, jsonField_conc]
  | .row e k, _ => by
    simp only [SVal.conc, fieldOf, SVal.field]
    rw [run_note_pure, conc_find_keyed, rowField_conc M e name k]
  | .single e, _ => by
    simp only [SVal.conc, fieldOf, SVal.field]
    rw [run_note_pure, conc_find_single]
    cases r.singles.lookup e with
    | none => rfl
    | some fields => simp [toVal_toValue?, jsonField_conc]
  | .obj fs, _ => by
    simp only [SVal.conc, fieldOf, SVal.field, run_pure, concFields_lookup]
    cases fs.lookup name <;> rfl
  | .table _, _ | .list _, _ | .emit .., _ => rfl
  | .ite c a b, h => by
    simp only [SVal.field, conc_ite] at h ⊢
    split
    · rename_i hc; simp only [hc, ite_true] at h; exact field_conc M r name s a h
    · rename_i hc; simp only [hc, Bool.false_eq_true, ite_false] at h; exact field_conc M r name s b h


theorem find_liveRows_isSome (M : Model) (e x : String) : ∀ ss : List Slot,
    ((liveRows M e ss).find? (fun row => row.entity == e && row.key == some x)).isSome =
      ss.any (fun s => s.live.holds M && decide ((s.key.denote M).toStr = x))
  | [] => rfl
  | s :: ss => by
    have ih := find_liveRows_isSome M e x ss
    by_cases hl : s.live.holds M
    · have hlr : liveRows M e (s :: ss) = Slot.row M e s :: liveRows M e ss := by simp [liveRows, hl]
      rw [hlr, List.find?_cons, List.any_cons, hl]
      by_cases hk : (s.key.denote M).toStr = x
      · have hp : ((Slot.row M e s).entity == e && (Slot.row M e s).key == some x) = true := by simp [Slot.row, hk]
        simp [hp, hk]
      · have hp : ((Slot.row M e s).entity == e && (Slot.row M e s).key == some x) = false := by simp [Slot.row, hk]
        rw [hp]
        simp [ih, hk]
    · have hlr : liveRows M e (s :: ss) = liveRows M e ss := by simp [liveRows, hl]
      rw [hlr, ih, List.any_cons]
      simp [hl]

theorem keyIn_holds (M : Model) (k : Term) : ∀ ss : List Slot,
    (keyIn k ss).holds M = ss.any (fun s => s.live.holds M && decide ((s.key.denote M).toStr = (k.denote M).toStr))
  | [] => rfl
  | s :: ss => by
    have ih := keyIn_holds M k ss
    simp only [keyIn, disj, List.map_cons, List.foldr_cons] at ih ⊢
    rw [holds_or, ih, holds_and, mkStr_eq_holds, List.any_cons]

theorem liveRows_filter_self (M : Model) (e : String) (ss : List Slot) :
    (liveRows M e ss).filter (·.entity == e) = liveRows M e ss := by
  simp [liveRows, List.filter_map, Function.comp_def, Slot.row]

theorem liveRows_filter_other (M : Model) (e e' : String) (he : e' ≠ e) (ss : List Slot) :
    (liveRows M e' ss).filter (·.entity == e) = [] := by
  simp [liveRows, List.filter_map, Function.comp_def, Slot.row, he]

theorem liveRows_keys_length (M : Model) (e : String) (ss : List Slot) :
    ((liveRows M e ss).filterMap (·.key)).length = (ss.filter (·.live.holds M)).length := by
  simp [liveRows, List.filterMap_map, Function.comp_def, Slot.row]

theorem any_eq_find (p : Row → Bool) (rows : Records) : rows.any p = (rows.find? p).isSome := by
  induction rows with
  | nil => rfl
  | cons r rs ih => cases h : p r <;> simp [h, ih]

theorem liveCount_denote (M : Model) : ∀ ss : List Slot,
    (liveCount ss).denote M = .int (ss.filter (·.live.holds M)).length
  | [] => rfl
  | s :: ss => by
    simp only [liveCount, Term.denote, liveCount_denote M ss, Lit.toInt, intLit]
    by_cases hl : s.live.holds M
    · simp only [Term.holds] at hl; simp [hl]; omega
    · simp only [Term.holds] at hl; simp [hl]

theorem keys_length (M : Model) (r : SRecords) (e : String) :
    ((r.conc M).keys e).length = ((r.slotsOf e).filter (·.live.holds M)).length := by
  simp only [Records.keys, List.length_mergeSort, SRecords.conc, List.filter_append, List.filterMap_append,
    List.length_append]
  have hs : ((r.singles.map fun (e, fields) => ({ entity := e, key := none, value := .obj (present M fields) } : Row)).filter
      (·.entity == e)).filterMap (·.key) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro row hrow
    simp only [List.mem_filter, List.mem_map] at hrow
    obtain ⟨⟨_, _, rfl⟩, _⟩ := hrow
    rfl
  rw [hs, List.length_nil, Nat.add_zero, SRecords.slotsOf]
  induction r.keyed with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨e', slots⟩ := p
    have hrow : (fun (x : String × List Slot) => List.map (Slot.row M x.1) (List.filter (fun s => s.live.holds M) x.2)) =
        fun x => liveRows M x.1 x.2 := rfl
    simp only [List.flatMap_cons, List.filter_append, List.filterMap_append, List.length_append, List.filter_cons]
      at ih ⊢
    rw [ih]
    by_cases he : e' = e
    · subst he
      simp only [beq_self_eq_true, ite_true, List.flatMap_cons, List.filter_append, List.length_append]
      have h1 := liveRows_filter_self M e' slots
      have h2 := liveRows_keys_length M e' slots
      simp only [liveRows] at h1 h2
      rw [h1, h2]
    · have : (e' == e) = false := by simp [he]
      have := liveRows_filter_other M e e' he slots
      simp only [liveRows] at this
      simp [*]


/-! ### Combinators: an evaluation step that agrees, followed by one that agrees. -/

theorem agrees_congr {M : Model} {recs : Records} {r r' : SRes} {x : Except Issue Val}
    (hv : r.1.conc M recs = r'.1.conc M recs) (he : r.2.holds M = r'.2.holds M) (h : Agrees M recs r x) :
    Agrees M recs r' x := by
  cases x with
  | ok v => obtain ⟨h1, h2⟩ := h; exact ⟨he ▸ h1, hv ▸ h2⟩
  | error _ => show r'.2.holds M = true; rw [← he]; exact h

theorem agrees_bind {M : Model} {recs : Records} {α : Type} {x : EvalM Val} {k : Val → EvalM α} {ra : SRes}
    {P : Except Issue α → Prop} (hx : ∀ s, Agrees M recs ra (run x s).1) (herr : ra.2.holds M = true → ∀ e, P (.error e))
    (hk : ∀ s, ra.2.holds M = false → P (run (k (ra.1.conc M recs)) s).1) (s : Trace) : P (run (x >>= k) s).1 := by
  rw [run_bind]
  have h := hx s
  rcases hr : run x s with ⟨r, s'⟩
  rw [hr] at h
  cases r with
  | error e => exact herr h e
  | ok v => obtain ⟨h1, h2⟩ := h; subst h2; exact hk s' h1

theorem nonScalar_ordinal (order : Order) {v : Val} (h : NonScalar v) : ordinal order v = none := by
  cases v with
  | json j => cases j <;> simp_all [NonScalar, ordinal]
  | _ => simp_all [NonScalar, ordinal]

theorem nonScalar_double {v : Val} (h : NonScalar v) : double? v = none := by
  cases v with
  | json j => cases j <;> simp_all [NonScalar, double?]
  | _ => simp_all [NonScalar, double?]

theorem toVal_ordinal (sc : Scalar) :
    ordinal .number sc.toVal = (match sc with | .int n => some (n, 0) | _ => none) := by
  cases sc <;> rfl

theorem toVal_not_nonFinite (sc : Scalar) (x : Float) : sc.toVal ≠ .nonFinite x := by
  cases sc <;> simp [Scalar.toVal, Scalar.toValue?, Val.ofOption]

theorem relT_holds (M : Model) (r : Relation) (a b : Term) :
    (relT r (.intOf a) (.intOf b)).holds M =
      r.holds (((Term.intOf a).denote M).toInt) (((Term.intOf b).denote M).toInt) := by
  cases r
  case eq =>
    simp only [relT, Relation.holds, Term.holds, Term.denote, Lit.toBool, Lit.toInt, Lit.int.injEq]
    exact (Bool.beq_eq_decide_eq _ _).symm
  all_goals rfl

/-- The value of `t` as a scalar, whether it is a scalar term or not. -/
theorem scalar_cases (M : Model) (recs : Records) (v : SVal) :
    (v.scalarOf.2.holds M = false ∧ v.conc M recs = (v.scalarOf.1.denote M).toScalar.toVal) ∨
      (v.scalarOf.2.holds M = true ∧ NonScalar (v.conc M recs)) := by
  have h := scalarOf_conc M recs v
  cases hv : v.scalarOf.2.holds M
  · exact .inl ⟨rfl, by simpa [conc_scalar] using h.1 hv⟩
  · exact .inr ⟨rfl, h.2 hv⟩


/-! ### Each operation on values that agree -/

theorem holds_isInt (M : Model) (t : Term) :
    (Term.isInt t).holds M = (match (t.denote M).toScalar with | .int _ => true | _ => false) := rfl
theorem holds_isStr (M : Model) (t : Term) :
    (Term.isStr t).holds M = (match (t.denote M).toScalar with | .str _ => true | _ => false) := rfl
theorem denote_intOf (M : Model) (t : Term) :
    ((Term.intOf t).denote M).toInt = (match (t.denote M).toScalar with | .int n => n | _ => 0) := rfl
theorem denote_strOf (M : Model) (t : Term) :
    ((Term.strOf t).denote M).toStr = (match (t.denote M).toScalar with | .str s => s | _ => "") := rfl

theorem compare_op (M : Model) (recs : Records) (r : Relation) (va vb : SVal) (s : Trace) :
    Agrees M recs (.scalar (.mkBool (relT r (.intOf va.scalarOf.1) (.intOf vb.scalarOf.1))),
        .or va.scalarOf.2 (.or vb.scalarOf.2 (.not (.and (.isInt va.scalarOf.1) (.isInt vb.scalarOf.1)))))
      (run (match va.conc M recs, vb.conc M recs, double? (va.conc M recs), double? (vb.conc M recs) with
        | .nonFinite _, _, some x, some y | _, .nonFinite _, some x, some y =>
          if Order.number == .number then pure (.json (.bool (r.holds x y))) else thrown
        | _, _, _, _ =>
          match ordinal .number (va.conc M recs), ordinal .number (vb.conc M recs) with
          | some (m, e), some (m', e') => pure (.json (.bool (r.holds (m * 10 ^ e') (m' * 10 ^ e))))
          | _, _ => thrown : EvalM Val) s).1 := by
  rcases scalar_cases M recs va with ⟨ha, hca⟩ | ⟨ha, hna⟩ <;>
    rcases scalar_cases M recs vb with ⟨hb, hcb⟩ | ⟨hb, hnb⟩
  · rw [hca, hcb]
    have nf1 := toVal_not_nonFinite (va.scalarOf.1.denote M).toScalar
    have nf2 := toVal_not_nonFinite (vb.scalarOf.1.denote M).toScalar
    split
    · exfalso; simp_all
    · exfalso; simp_all
    · rw [toVal_ordinal, toVal_ordinal]
      cases hx : (va.scalarOf.1.denote M).toScalar <;> cases hy : (vb.scalarOf.1.denote M).toScalar <;>
        simp [run_pure, run_thrown, Agrees, holds_or, holds_not, holds_and, ha, hb, hx, hy, holds_isInt, relT_holds,
          denote_intOf, conc_mkBool]
  · rw [nonScalar_double hnb, nonScalar_ordinal .number hnb]
    split <;> simp_all [run_thrown, Agrees, holds_or]
  · rw [nonScalar_double hna, nonScalar_ordinal .number hna]
    split <;> simp_all [run_thrown, Agrees, holds_or]
  · rw [nonScalar_double hna, nonScalar_ordinal .number hna]
    split <;> simp_all [run_thrown, Agrees, holds_or]


theorem strLen_op (M : Model) (recs : Records) (v : SVal) (s : Trace) :
    Agrees M recs (.scalar (.mkInt (.len (.strOf v.scalarOf.1))), .or v.scalarOf.2 (.not (.isStr v.scalarOf.1)))
      (run (match v.conc M recs with
        | .json (.str s) => pure (.json (.num s.length))
        | _ => thrown : EvalM Val) s).1 := by
  rcases scalar_cases M recs v with ⟨h, hc⟩ | ⟨h, hn⟩
  · rw [hc]
    cases hx : (v.scalarOf.1.denote M).toScalar <;>
      simp [Scalar.toVal, Scalar.toValue?, Val.ofOption, run_pure, run_thrown, Agrees, holds_or, holds_not, h,
        holds_isStr, hx, conc_mkInt, Term.denote, Lit.toInt]
    rfl
  · split
    · rename_i hv; rw [hv] at hn; exact absurd hn (by simp [NonScalar])
    · simp [run_thrown, Agrees, holds_or, h]

theorem strings_op (M : Model) (recs : Records) (vs vp : SVal) (es ep : Term) (f : String → String → Bool)
    (t : Term → Term → Term) (ht : ∀ x y, ((t x y).holds M) = f ((y.denote M).toStr) ((x.denote M).toStr))
    (hes : es.holds M = false) (hep : ep.holds M = false) (s : Trace) :
    Agrees M recs (.scalar (.mkBool (t (stringsOf (vs, es) (vp, ep)).1 (stringsOf (vs, es) (vp, ep)).2.1)),
        (stringsOf (vs, es) (vp, ep)).2.2)
      (run (strings (vs.conc M recs) (vp.conc M recs) >>= fun (s, p) => pure (.json (.bool (f p s))) : EvalM Val)
        s).1 := by
  rw [run_bind]
  simp only [stringsOf]
  rcases scalar_cases M recs vs with ⟨h, hc⟩ | ⟨h, hn⟩ <;>
    rcases scalar_cases M recs vp with ⟨h', hc'⟩ | ⟨h', hn'⟩
  · rw [hc, hc']
    cases hx : (vs.scalarOf.1.denote M).toScalar <;> cases hy : (vp.scalarOf.1.denote M).toScalar <;>
      simp [strings, Scalar.toVal, Scalar.toValue?, Val.ofOption, run_pure, run_thrown, Agrees, holds_or, holds_not,
        holds_and, h, h', hes, hep, holds_isStr, hx, hy, conc_mkBool, ht, denote_strOf]
  all_goals
    have hthrow : strings (vs.conc M recs) (vp.conc M recs) = thrown := by
      unfold strings; split <;> simp_all [NonScalar]
    rw [hthrow, run_thrown]
    simp [Agrees, holds_or, h, h']

theorem arith_op (M : Model) (recs : Records) (op : Arith) (va vb : SVal) (s : Trace) :
    Agrees M recs (.scalar (.mkInt (arithT op (.intOf va.scalarOf.1) (.intOf vb.scalarOf.1))),
        .or va.scalarOf.2 (.or vb.scalarOf.2 (.not (.and (.isInt va.scalarOf.1) (.isInt vb.scalarOf.1)))))
      (run (match integer? (va.conc M recs), integer? (vb.conc M recs) with
        | some x, some y => pure (.json (.num (op.apply x y)))
        | _, _ => thrown : EvalM Val) s).1 := by
  have hint : ∀ v : SVal, v.scalarOf.2.holds M = true → integer? (v.conc M recs) = none := by
    intro v h
    rcases scalar_cases M recs v with ⟨h', _⟩ | ⟨_, hn⟩
    · simp [h] at h'
    · revert hn; cases v.conc M recs with
      | json j => cases j <;> simp [NonScalar, integer?]
      | _ => simp [NonScalar, integer?]
  have hsc : ∀ sc : Scalar, integer? sc.toVal = (match sc with | .int n => some n | _ => none) := by
    intro sc; cases sc <;> simp [Scalar.toVal, Scalar.toValue?, Val.ofOption, integer?]
  rcases scalar_cases M recs va with ⟨ha, hca⟩ | ⟨ha, hna⟩ <;>
    rcases scalar_cases M recs vb with ⟨hb, hcb⟩ | ⟨hb, hnb⟩
  · rw [hca, hcb, hsc, hsc]
    cases hx : (va.scalarOf.1.denote M).toScalar <;> cases hy : (vb.scalarOf.1.denote M).toScalar <;>
      simp [run_pure, run_thrown, Agrees, holds_or, holds_not, holds_and, ha, hb, hx, hy, holds_isInt, conc_mkInt,
        ]
    all_goals cases op <;> simp [arithT, Term.denote, Lit.toInt, hx, hy, Arith.apply, Lean.JsonNumber.fromInt]
  all_goals simp [hint va, hint vb, ha, hb, run_thrown, Agrees, holds_or]


theorem conc_any_keyed (M : Model) (r : SRecords) (e : String) (k : Term) :
    (r.conc M).any (fun row => row.entity == e && row.key == some (k.denote M).toStr) =
      (keyIn k (r.slotsOf e)).holds M := by
  rw [any_eq_find, conc_find_keyed, find_liveRows_isSome, keyIn_holds]

theorem lookup_op (M : Model) (r : SRecords) (vk : SVal) (s : Trace) : ∀ vt : SVal,
    Agrees M (r.conc M) (SVal.lookup r vk vt)
      (run (match vt.conc M (r.conc M), vk.conc M (r.conc M) with
        | .table source entity, .json (.str key) => do
          note (.record entity key)
          pure (if source.any (fun r => r.entity == entity && r.key == some key) then .row source entity (some key)
            else .undef)
        | _, _ => thrown : EvalM Val) s).1
  | .table e => by
    simp only [SVal.lookup, SVal.conc]
    rcases scalar_cases M (r.conc M) vk with ⟨h, hc⟩ | ⟨h, hn⟩
    · rw [hc]
      cases hx : (vk.scalarOf.1.denote M).toScalar with
      | str key =>
        simp only [Scalar.toVal, Scalar.toValue?, Val.ofOption]
        rw [run_note_pure]
        have hk : ((Term.strOf vk.scalarOf.1).denote M).toStr = key := by simp [denote_strOf, hx]
        have := conc_any_keyed M r e (.strOf vk.scalarOf.1)
        rw [hk] at this
        rw [this]
        refine ⟨by simp [holds_or, holds_not, h, holds_isStr, hx], ?_⟩
        simp only [SVal.conc, hk]
        rfl
      | _ => simp [Scalar.toVal, Scalar.toValue?, Val.ofOption, run_thrown, Agrees, holds_or, holds_not, holds_isStr, hx]
    · split
      · rename_i hv; rw [hv] at hn; exact absurd hn (by simp [NonScalar])
      · simp [run_thrown, Agrees, holds_or, h]
  | .ite c a b => by
    have ha := lookup_op M r vk s a
    have hb := lookup_op M r vk s b
    simp only [SVal.lookup, conc_ite]
    by_cases hc : c.holds M
    · simp only [hc, ite_true]; exact agrees_congr (by simp [conc_ite, hc]) (by simp [holds_ite, hc]) ha
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact agrees_congr (by simp [conc_ite, hc]) (by simp [holds_ite, hc]) hb
  | .scalar t => by
    simp only [SVal.lookup, SVal.conc]
    cases (t.denote M).toScalar <;> simp [Scalar.toVal, Scalar.toValue?, Val.ofOption, run_thrown, Agrees, holds_tt]
  | .json _ | .row .. | .single _ | .obj _ | .list _ | .emit .. => by
    simp [SVal.lookup, SVal.conc, run_thrown, Agrees, holds_tt]

theorem size_op (M : Model) (r : SRecords) (s : Trace) : ∀ v : SVal,
    Agrees M (r.conc M) (SVal.size r v)
      (run (match v.conc M (r.conc M) with
        | .json (.arr vs) => pure (.json (.num vs.length))
        | .list vs => pure (.json (.num vs.length))
        | .table source entity => do
          note (.keys entity)
          pure (.json (.num (source.keys entity).length))
        | _ => thrown : EvalM Val) s).1
  | .table e => by
    simp only [SVal.size, SVal.conc]
    rw [run_note_pure]
    refine ⟨holds_ff M, ?_⟩
    simp [conc_mkInt, liveCount_denote, Lit.toInt, keys_length]
    rfl
  | .list vs => by
    simp only [SVal.size, SVal.conc, run_pure]
    refine ⟨holds_ff M, ?_⟩
    have : (SVal.concAll M (r.conc M) vs).length = vs.length := by
      induction vs with
      | nil => rfl
      | cons _ _ ih => simp [SVal.concAll, ih]
    simp [conc_mkInt, Term.denote, Lit.toInt, intLit, this]
    rfl
  | .ite c a b => by
    have ha := size_op M r s a
    have hb := size_op M r s b
    simp only [SVal.size, conc_ite]
    by_cases hc : c.holds M
    · simp only [hc, ite_true]; exact agrees_congr (by simp [conc_ite, hc]) (by simp [holds_ite, hc]) ha
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact agrees_congr (by simp [conc_ite, hc]) (by simp [holds_ite, hc]) hb
  | .scalar t => by
    simp only [SVal.size, SVal.conc]
    cases (t.denote M).toScalar <;> simp [Scalar.toVal, Scalar.toValue?, Val.ofOption, run_thrown, Agrees, holds_tt]
  | .json _ | .row .. | .single _ | .obj _ | .emit .. => by
    simp [SVal.size, SVal.conc, run_thrown, Agrees, holds_tt]


theorem any_same_conc (M : Model) (recs : Records) (vv : SVal) : ∀ vs : List SVal,
    (SVal.concAll M recs vs).any (same · (vv.conc M recs)) = (SVal.includes vv (.list vs)).1.holds M
  | [] => rfl
  | v :: vs => by
    have ih := any_same_conc M recs vv vs
    simp only [SVal.includes, SVal.concAll, List.any_cons, List.map_cons, disj, List.foldr_cons] at ih ⊢
    rw [holds_or, same_conc M recs v vv, ih]

theorem concAll_append (M : Model) (recs : Records) (xs ys : List SVal) :
    SVal.concAll M recs (xs ++ ys) = SVal.concAll M recs xs ++ SVal.concAll M recs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SVal.concAll, ih]

theorem elements_op (M : Model) (recs : Records) (vv : SVal) (s : Trace) : ∀ va : SVal,
    ((SVal.includes vv va).2.holds M = true → ∃ e, (run (elements (va.conc M recs)) s).1 = .error e) ∧
      ((SVal.includes vv va).2.holds M = false → ∃ L, (run (elements (va.conc M recs)) s).1 = .ok L ∧
        L.any (same · (vv.conc M recs)) = (SVal.includes vv va).1.holds M)
  | .list vs => by
    refine ⟨fun h => by simp [SVal.includes, holds_ff] at h, fun _ => ⟨_, rfl, any_same_conc M recs vv vs⟩⟩
  | .table e => by
    refine ⟨fun h => by simp [SVal.includes, holds_ff] at h, fun _ => ⟨_, run_note_pure _ _ s, ?_⟩⟩
    simp [SVal.includes, holds_ff, same]
  | .ite c a b => by
    have ha := elements_op M recs vv s a
    have hb := elements_op M recs vv s b
    simp only [SVal.includes, conc_ite, holds_ite]
    by_cases hc : c.holds M <;> simp only [hc, ite_true, Bool.false_eq_true, ite_false] <;> assumption
  | .scalar t => by
    refine ⟨fun _ => ⟨.thrown none, ?_⟩, fun h => by simp [SVal.includes, holds_tt] at h⟩
    simp only [SVal.conc]
    cases (t.denote M).toScalar <;> rfl
  | .json _ | .row .. | .single _ | .obj _ | .emit .. => by
    refine ⟨fun _ => ⟨.thrown none, rfl⟩, fun h => by simp [SVal.includes, holds_tt] at h⟩

/-- The environment that `env` is under `M`, with the field names `fields`, which no encoded operation reads. -/
def concEnv (M : Model) (env : SEnv) (fields : String → List String) : Env :=
  { args := fun a => ((env.args a).map (·.conc M (env.records.conc M))).getD .undef,
    records := env.records.conc M, fields, keys := {}, hidden := false }

def concVars (M : Model) (recs : Records) (vars : List (String × SVal)) : List (String × Val) :=
  vars.map fun (x, v) => (x, v.conc M recs)

theorem concVars_lookup (M : Model) (recs : Records) (x : String) : ∀ vars : List (String × SVal),
    (concVars M recs vars).lookup x = (vars.lookup x).map (·.conc M recs)
  | [] => rfl
  | (y, v) :: vars => by
    have ih := concVars_lookup M recs x vars
    simp only [concVars] at ih ⊢
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all

/-- That `r` is what a list of evaluations `x` gives under `M`. -/
def AgreesAll (M : Model) (recs : Records) (r : List SVal × Term) (x : Except Issue (List Val)) : Prop :=
  match x with
  | .ok vs => r.2.holds M = false ∧ vs = SVal.concAll M recs r.1
  | .error _ => r.2.holds M = true

def AgreesFields (M : Model) (recs : Records) (r : List (String × SVal) × Term)
    (x : Except Issue (List (String × Val))) : Prop :=
  match x with
  | .ok fs => r.2.holds M = false ∧ fs = SVal.concFields M recs r.1
  | .error _ => r.2.holds M = true

theorem litTerm_conc (M : Model) (v : Value) (t : Term) (h : litTerm v = .ok t) :
    (t.denote M).toScalar.toVal = .json v := by
  cases v with
  | null => cases h; rfl
  | bool b => cases h; rfl
  | num n =>
    simp only [litTerm] at h
    split at h
    · cases h; rename_i he
      have : n.exponent = 0 := by simpa using he
      cases n; simp_all [Term.denote, Lit.toScalar, Scalar.toVal, Scalar.toValue?, Val.ofOption]
    · cases h
  | str s =>
    simp only [litTerm] at h
    split at h
    · cases h; rfl
    · cases h
  | arr _ | obj _ => cases h


theorem agrees_err {M : Model} {recs : Records} {r : SRes} {e' : Term} {x : Except Issue Val}
    (he : r.2.holds M = e'.holds M) (h : Agrees M recs r x) : Agrees M recs (r.1, e') x :=
  agrees_congr (r := r) rfl he h

mutual

/-- The encoding agrees with Ir.eval: under every model, from every state of the evaluation's trace. -/
@[guarantee] theorem seval_agrees (M : Model) (env : SEnv) (fields : String → List String) :
    ∀ (vars : List (String × SVal)) (e : Expr) (r : SRes), seval env vars e = .ok r → ∀ s,
      Agrees M (env.records.conc M) r
        (run (eval (concEnv M env fields) (concVars M (env.records.conc M) vars) e) s).1
  | vars, .undef, r, h, s => by cases h; exact ⟨rfl, rfl⟩
  | vars, .lit v, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i t ht; cases h; exact ⟨rfl, (litTerm_conc M v t ht).symm⟩
  | vars, .arg a, r, h, s => by
    cases h
    refine ⟨rfl, ?_⟩
    simp only [concEnv]
    cases env.args a <;> rfl
  | vars, .var x, r, h, s => by
    simp only [seval] at h
    simp only [eval, concVars_lookup]
    cases hx : vars.lookup x with
    | none => rw [hx] at h; cases h; exact holds_tt M
    | some v => rw [hx] at h; cases h; exact ⟨rfl, rfl⟩
  | vars, .let x e body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i re hre
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars e re hre) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    have h2 := seval_agrees M env fields ((x, re.1) :: vars) body rb hrb s1
    simp only [concVars, List.map_cons] at h2 ⊢
    exact agrees_congr (r := rb) rfl (by simp [holds_or, h1]) h2
  | vars, .ite c yes no, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    · contradiction
    rename_i ry hry
    split at h
    · contradiction
    rename_i rn hrn
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars c rc hrc) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    rw [← truthy_conc]
    by_cases ht : rc.1.truthy.holds M
    · simp only [ht, ite_true]
      exact agrees_congr (by simp [conc_ite, ht]) (by simp [holds_or, holds_ite, h1, ht])
        (seval_agrees M env fields vars yes ry hry s1)
    · simp only [ht, Bool.false_eq_true, ite_false]
      exact agrees_congr (by simp [conc_ite, ht]) (by simp [holds_or, holds_ite, h1, ht])
        (seval_agrees M env fields vars no rn hrn s1)
  | vars, .and a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    rw [← truthy_conc]
    by_cases ht : ra.1.truthy.holds M
    · simp only [ht, ite_true]
      exact agrees_congr (by simp [conc_ite, ht]) (by simp [holds_or, holds_and, h1, ht])
        (seval_agrees M env fields vars b rb hrb s1)
    · simp only [ht, Bool.false_eq_true, ite_false, run_pure]
      exact ⟨by simp [holds_or, holds_and, h1, ht], by simp [conc_ite, ht]⟩
  | vars, .or a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    rw [← truthy_conc]
    by_cases ht : ra.1.truthy.holds M
    · simp only [ht, ite_true, run_pure]
      exact ⟨by simp [holds_or, holds_and, holds_not, h1, ht], by simp [conc_ite, ht]⟩
    · simp only [ht, Bool.false_eq_true, ite_false]
      exact agrees_congr (by simp [conc_ite, ht]) (by simp [holds_or, holds_and, holds_not, h1, ht])
        (seval_agrees M env fields vars b rb hrb s1)
  | vars, .coalesce a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    have hn := nullish_conc M (env.records.conc M) ra.1
    split
    · rename_i hv
      rw [hv] at hn
      simp only [isNullish] at hn
      exact agrees_congr (by simp [conc_ite, hn]) (by simp [holds_or, holds_and, h1, hn])
        (seval_agrees M env fields vars b rb hrb s1)
    · rename_i hv
      rw [hv] at hn
      simp only [isNullish] at hn
      exact agrees_congr (by simp [conc_ite, hn]) (by simp [holds_or, holds_and, h1, hn])
        (seval_agrees M env fields vars b rb hrb s1)
    · rename_i v hu hnl
      have : isNullish (ra.1.conc M (env.records.conc M)) = false := by
        revert hu hnl; cases ra.1.conc M (env.records.conc M) with
        | undef => simp
        | json j => cases j <;> simp [isNullish]
        | _ => simp [isNullish]
      rw [this] at hn
      exact ⟨by simp [holds_or, holds_and, h1, hn], by simp [conc_ite, hn]⟩
  | vars, .not a, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, h1]) ?_ s
    intro s1 h1
    exact ⟨h1, by simp [conc_mkBool, holds_not, truthy_conc M (env.records.conc M)]⟩
  | vars, .eq a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s1
    intro s2 h2
    exact ⟨by simp [holds_or, h1, h2], by simp [conc_mkBool, same_conc M (env.records.conc M)]⟩
  | vars, .compare rel .number a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s1
    intro s2 h2
    exact agrees_err (by simp [holds_or, h1, h2]) (compare_op M _ rel ra.1 rb.1 s2)
  | vars, .compare _ .date _ _, r, h, s => by simp [seval] at h
  | vars, .field a name, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    have hn := nullish_conc M (env.records.conc M) ra.1
    split
    · rename_i hv; rw [hv] at hn
      simp [run_thrown, Agrees, holds_or, hn, isNullish]
    · rename_i hv; rw [hv] at hn
      simp [run_thrown, Agrees, holds_or, hn, isNullish]
    · rename_i v hu hnl
      have hnn : isNullish (ra.1.conc M (env.records.conc M)) = false := by
        revert hu hnl; cases ra.1.conc M (env.records.conc M) with
        | undef => simp
        | json j => cases j <;> simp [isNullish]
        | _ => simp [isNullish]
      rw [field_conc M env.records name s1 ra.1 hnn]
      exact ⟨by simp [holds_or, h1, hn, hnn], rfl⟩
  | vars, .fieldOpt a name, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, h1]) ?_ s
    intro s1 h1
    have hn := nullish_conc M (env.records.conc M) ra.1
    split
    · rename_i hv; rw [hv] at hn
      exact ⟨h1, by simp [conc_ite, hn, isNullish, conc_undef]⟩
    · rename_i hv; rw [hv] at hn
      exact ⟨h1, by simp [conc_ite, hn, isNullish, conc_undef]⟩
    · rename_i v hu hnl
      have hnn : isNullish (ra.1.conc M (env.records.conc M)) = false := by
        revert hu hnl; cases ra.1.conc M (env.records.conc M) with
        | undef => simp
        | json j => cases j <;> simp [isNullish]
        | _ => simp [isNullish]
      rw [field_conc M env.records name s1 ra.1 hnn]
      exact ⟨h1, by simp [conc_ite, hn, hnn]⟩
  | vars, .strLen a, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    exact agrees_err (by simp [holds_or, h1]) (strLen_op M _ ra.1 s1)
  | vars, .startsWith a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, stringsOf, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, stringsOf, h2]) ?_ s1
    intro s2 h2
    exact strings_op M _ ra.1 rb.1 ra.2 rb.2 (fun p s => p.toList.isPrefixOf s.toList) (fun x y => .prefixOf y x)
      (fun _ _ => rfl) h1 h2 s2
  | vars, .endsWith a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, stringsOf, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, stringsOf, h2]) ?_ s1
    intro s2 h2
    exact strings_op M _ ra.1 rb.1 ra.2 rb.2 (fun p s => p.toList.reverse.isPrefixOf s.toList.reverse)
      (fun x y => .suffixOf y x) (fun _ _ => rfl) h1 h2 s2
  | vars, .strIncludes a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, stringsOf, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, stringsOf, h2]) ?_ s1
    intro s2 h2
    exact strings_op M _ ra.1 rb.1 ra.2 rb.2 (fun p s => isInfix p.toList s.toList) (fun x y => .contains x y)
      (fun _ _ => rfl) h1 h2 s2
  | vars, .size a, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    exact agrees_err (by simp [holds_or, h1]) (size_op M env.records s1 ra.1)
  | vars, .table e, r, h, s => by cases h; exact ⟨rfl, rfl⟩
  | vars, .single e, r, h, s => by cases h; exact ⟨rfl, rfl⟩
  | vars, .lookup a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s1
    intro s2 h2
    exact agrees_err (by simp [holds_or, h1, h2]) (lookup_op M env.records rb.1 s2 ra.1)
  | vars, .obj fs, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rf hrf
    cases h
    simp only [eval]
    rw [run_bind]
    have := sevalFields_agrees M env fields vars fs rf hrf s
    rcases hr : run (evalFields (concEnv M env fields) (concVars M (env.records.conc M) vars) fs) s with ⟨x, s1⟩
    rw [hr] at this
    cases x with
    | error => exact this
    | ok vs => obtain ⟨h1, h2⟩ := this; exact ⟨h1, by simp [SVal.conc, h2]⟩
  | vars, .arr es, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rf hrf
    cases h
    simp only [eval]
    rw [run_bind]
    have := sevalAll_agrees M env fields vars es rf hrf s
    rcases hr : run (evalAll (concEnv M env fields) (concVars M (env.records.conc M) vars) es) s with ⟨x, s1⟩
    rw [hr] at this
    cases x with
    | error => exact this
    | ok vs => obtain ⟨h1, h2⟩ := this; exact ⟨h1, by simp [SVal.conc, h2]⟩
  | vars, .concat a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    split at h
    · rename_i xs ys _ _
      cases h
      simp only [eval]
      refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
      intro s1 h1
      refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
        (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s1
      intro s2 h2
      rename_i hxs hys
      rw [hxs, hys]
      simp only [SVal.conc, elements, run_pure, run_bind]
      exact ⟨by simp [holds_or, h1, h2], by simp [SVal.conc, concAll_append]⟩
    · contradiction
  | vars, .includes a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    rw [run_bind]
    have he := elements_op M (env.records.conc M) rb.1 s1 ra.1
    rcases hr : run (elements (ra.1.conc M (env.records.conc M))) s1 with ⟨x, s2⟩
    rw [hr] at he
    cases hi : (SVal.includes rb.1 ra.1).2.holds M with
    | true =>
      obtain ⟨e, he⟩ := he.1 hi
      cases he
      simp [Agrees, holds_or, hi]
    | false =>
      obtain ⟨L, hL, hany⟩ := he.2 hi
      cases hL
      refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
        (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s2
      intro s3 h2
      exact ⟨by simp [holds_or, h1, h2, hi], by simp [conc_mkBool, hany]⟩
  | vars, .arith op a b, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
      (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s1
    intro s2 h2
    exact agrees_err (by simp [holds_or, h1, h2]) (arith_op M _ op ra.1 rb.1 s2)
  | vars, .emit ev a, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, h1]) ?_ s
    intro s1 h1
    exact ⟨h1, by simp [SVal.conc]⟩
  | vars, .filter .., r, h, s | vars, .some .., r, h, s | vars, .every .., r, h, s | vars, .map .., r, h, s
  | vars, .sum .., r, h, s | vars, .min .., r, h, s | vars, .max .., r, h, s | vars, .only _, r, h, s
  | vars, .sortedBy .., r, h, s | vars, .format _, r, h, s | vars, .decimal .., r, h, s | vars, .addDays .., r, h, s
  | vars, .createKey _, r, h, s => by simp [seval] at h

theorem sevalAll_agrees (M : Model) (env : SEnv) (fields : String → List String) (vars : List (String × SVal)) :
    ∀ (es : List Expr) (r : List SVal × Term), sevalAll env vars es = .ok r → ∀ s,
      AgreesAll M (env.records.conc M) r
        (run (evalAll (concEnv M env fields) (concVars M (env.records.conc M) vars) es) s).1
  | [], r, h, s => by cases h; exact ⟨rfl, rfl⟩
  | e :: es, r, h, s => by
    simp only [sevalAll, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i re hre
    split at h
    · contradiction
    rename_i rs hrs
    cases h
    simp only [evalAll]
    refine agrees_bind (P := AgreesAll M _ _) (seval_agrees M env fields vars e re hre)
      (fun h1 _ => by simp [AgreesAll, holds_or, h1]) ?_ s
    intro s1 h1
    rw [run_bind]
    have := sevalAll_agrees M env fields vars es rs hrs s1
    rcases hr : run (evalAll (concEnv M env fields) (concVars M (env.records.conc M) vars) es) s1 with ⟨x, s2⟩
    rw [hr] at this
    cases x with
    | error => simpa [AgreesAll, holds_or, h1] using this
    | ok vs => obtain ⟨h2, h3⟩ := this; exact ⟨by simp [holds_or, h1, h2], by simp [SVal.concAll, h3]⟩

theorem sevalFields_agrees (M : Model) (env : SEnv) (fields : String → List String) (vars : List (String × SVal)) :
    ∀ (fs : List Field) (r : List (String × SVal) × Term), sevalFields env vars fs = .ok r → ∀ s,
      AgreesFields M (env.records.conc M) r
        (run (evalFields (concEnv M env fields) (concVars M (env.records.conc M) vars) fs) s).1
  | [], r, h, s => by cases h; exact ⟨rfl, rfl⟩
  | ⟨name, e⟩ :: fs, r, h, s => by
    simp only [sevalFields, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i re hre
    split at h
    · contradiction
    rename_i rs hrs
    cases h
    simp only [evalFields]
    refine agrees_bind (P := AgreesFields M _ _) (seval_agrees M env fields vars e re hre)
      (fun h1 _ => by simp [AgreesFields, holds_or, h1]) ?_ s
    intro s1 h1
    rw [run_bind]
    have := sevalFields_agrees M env fields vars fs rs hrs s1
    rcases hr : run (evalFields (concEnv M env fields) (concVars M (env.records.conc M) vars) fs) s1 with ⟨x, s2⟩
    rw [hr] at this
    cases x with
    | error => simpa [AgreesFields, holds_or, h1] using this
    | ok vs =>
      obtain ⟨h2, h3⟩ := this; exact ⟨by simp [holds_or, h1, h2], by simp [SVal.concFields, h3]⟩

end

end Tazuna.Thm.Smt.Encode
