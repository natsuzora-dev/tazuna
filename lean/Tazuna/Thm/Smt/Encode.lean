import Tazuna.Smt.Encode
import Tazuna.Thm.Smt.Date
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
  | .json _ | .row .. | .single _ | .table _ | .obj _ | .list _ | .bag _ | .emit .. => rfl

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
  | .json _ | .row .. | .single _ | .table _ | .obj _ | .list _ | .bag _ | .emit .. => rfl

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
  | .scalar t, .bag _
  | .scalar t, .emit .. => by
    simp only [SVal.same, holds_ff, SVal.conc]
    cases (t.denote M).toScalar <;> rfl
  | .json _, w => by
    cases w <;> simp [SVal.same, SVal.conc, same_json_left, holds_ff]
  | .row .., w | .single _, w | .table _, w | .obj _, w | .list _, w | .bag _, w | .emit .., w => by
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
  | .json _ | .row .. | .single _ | .table _ | .obj _ | .list _ | .bag _ | .emit .. => by
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
  | .table _, _ | .list _, _ | .bag _, _ | .emit .., _ => rfl
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

theorem toVal_ordinal (sc : Scalar) :
    ordinal .number sc.toVal = (match sc with | .int n => some (n, 0) | _ => none) := by
  cases sc <;> rfl

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
      (run (match ordinal .number (va.conc M recs), ordinal .number (vb.conc M recs) with
        | some (m, e), some (m', e') => pure (.json (.bool (r.holds (m * 10 ^ e') (m' * 10 ^ e))))
        | _, _ => thrown : EvalM Val) s).1 := by
  rcases scalar_cases M recs va with ⟨ha, hca⟩ | ⟨ha, hna⟩ <;>
    rcases scalar_cases M recs vb with ⟨hb, hcb⟩ | ⟨hb, hnb⟩
  · rw [hca, hcb, toVal_ordinal, toVal_ordinal]
    cases hx : (va.scalarOf.1.denote M).toScalar <;> cases hy : (vb.scalarOf.1.denote M).toScalar <;>
      simp [run_pure, run_thrown, Agrees, holds_or, holds_not, holds_and, ha, hb, hx, hy, holds_isInt, relT_holds,
        denote_intOf, conc_mkBool]
  · rw [nonScalar_ordinal .number hnb]
    split <;> simp_all [run_thrown, Agrees, holds_or]
  · rw [nonScalar_ordinal .number hna]
    split <;> simp_all [run_thrown, Agrees, holds_or]
  · rw [nonScalar_ordinal .number hna]
    split <;> simp_all [run_thrown, Agrees, holds_or]


theorem relT_ints (M : Model) (r : Relation) (a b : Term) (x y : Int) (ha : a.denote M = .int x)
    (hb : b.denote M = .int y) : (relT r a b).holds M = r.holds x y := by
  cases r
  case eq =>
    simp only [relT, Relation.holds, Term.holds, Term.denote, ha, hb, Lit.toBool, Lit.int.injEq]
    exact (Bool.beq_eq_decide_eq _ _).symm
  all_goals simp [relT, Relation.holds, Term.holds, Term.denote, ha, hb, Lit.toBool, Lit.toInt]

theorem toVal_ordinal_date (sc : Scalar) :
    ordinal .date sc.toVal = (match sc with | .str s => (parseDate? s).map (·, 0) | _ => none) := by
  cases sc <;> rfl

/-- That the scalar term `t` is a date label, as eval parses it. -/
theorem dateT_holds (M : Model) (t : Term) :
    (dateT t).holds M = (match (t.denote M).toScalar with | .str s => isDateLabel s | _ => false) := by
  simp only [dateT, holds_and, holds_isStr, Tazuna.Thm.Smt.Date.dateValidT_holds, denote_strOf]
  cases (t.denote M).toScalar <;> simp

theorem dayT_strOf (M : Model) (t : Term) (s : String) (h : (t.denote M).toScalar = .str s) :
    (dayT (.strOf t)).denote M = .int (daysFromCivil (labelYear s) (labelMonth s) (labelDay s)) := by
  rw [Tazuna.Thm.Smt.Date.dayT_denote, denote_strOf, h]

theorem isDateLabel_empty : isDateLabel "" = false := rfl

/-- The label of the day number `z`, as a scalar, is a date label exactly when `z` is within the labelled days. -/
theorem dateLabel_scalar (M : Model) (z : Term) :
    match ((Term.mkStr (.dateLabel z)).denote M).toScalar with
    | .str s => isDateLabel s = (inRangeT z).holds M ∧
        (isDateLabel s = true → daysFromCivil (labelYear s) (labelMonth s) (labelDay s) = (z.denote M).toInt)
    | _ => False := by
  simp only [Term.denote, Lit.toScalar, Lit.toStr, Tazuna.Thm.Smt.Date.inRangeT_holds]
  cases h : renderDate? (z.denote M).toInt with
  | none => simp [isDateLabel_empty]
  | some s =>
    have hp := Tazuna.Thm.Data.Time.parse_render _ s h
    unfold parseDate? at hp
    split at hp
    · rename_i hl
      have hd := Option.some.inj hp
      simp only [Option.getD_some, Option.isSome_some, hl, true_and]
      exact fun _ => hd
    · cases hp

theorem inRangeT_label (M : Model) (z : Term) : (inRangeT z).holds M = (match ((Term.mkStr (.dateLabel z)).denote M).toScalar with
    | .str s => isDateLabel s | _ => false) := by
  have := dateLabel_scalar M z
  split at this
  · exact this.1.symm
  · exact this.elim

/-- That the scalar `t` is a date label, as eval parses it, read as `isDateOf` reads it. -/
theorem isDateOf_holds (M : Model) (t : Term) :
    (isDateOf t).holds M = (match (t.denote M).toScalar with | .str s => isDateLabel s | _ => false) := by
  fun_induction isDateOf t
  · exact inRangeT_label M _
  · exact inRangeT_label M _
  · rename_i c a b iha ihb
    simp only [Term.holds, Term.denote] at iha ihb ⊢
    by_cases hc : (c.denote M).toBool <;> simp [hc, iha, ihb]
  · rename_i v
    cases v <;> try rfl
    rename_i sc
    cases sc <;> rfl
  · exact dateT_holds M _

theorem label_day (M : Model) (z : Term) (s : String) (hn : ∃ n, z.denote M = .int n)
    (hs : ((Term.mkStr (.dateLabel z)).denote M).toScalar = .str s) (hv : isDateLabel s = true) :
    z.denote M = .int (daysFromCivil (labelYear s) (labelMonth s) (labelDay s)) := by
  obtain ⟨n, hn⟩ := hn
  have := dateLabel_scalar M z
  rw [hs] at this
  rw [this.2 hv, hn]; rfl

/-- The day number of the date label `t`, read as `dayOf` reads it, is the one that parseDate? gives. -/
theorem dayOf_denote (M : Model) (t : Term) (s : String) (h : (t.denote M).toScalar = .str s)
    (hv : isDateLabel s = true) : (dayOf t).denote M = .int (daysFromCivil (labelYear s) (labelMonth s) (labelDay s)) := by
  fun_induction dayOf t
  · exact label_day M _ s ⟨_, rfl⟩ h hv
  · exact label_day M _ s ⟨_, rfl⟩ h hv
  · rename_i c a b iha ihb
    simp only [Term.denote] at h ⊢
    by_cases hc : (c.denote M).toBool <;> simp only [hc, ite_true, Bool.false_eq_true, ite_false] at h ⊢
    · exact iha h
    · exact ihb h
  · rename_i v
    cases v <;> simp only [Term.denote, Lit.toScalar] at h <;> try (cases h)
    all_goals rfl
  · exact dayT_strOf M _ s h

theorem dateCompare_op (M : Model) (recs : Records) (r : Relation) (va vb : SVal) (s : Trace) :
    Agrees M recs (.scalar (.mkBool (relT r (dayOf va.scalarOf.1) (dayOf vb.scalarOf.1))),
        .or va.scalarOf.2 (.or vb.scalarOf.2 (.not (.and (isDateOf va.scalarOf.1) (isDateOf vb.scalarOf.1)))))
      (run (match ordinal .date (va.conc M recs), ordinal .date (vb.conc M recs) with
        | some (m, e), some (m', e') => pure (.json (.bool (r.holds (m * 10 ^ e') (m' * 10 ^ e))))
        | _, _ => thrown : EvalM Val) s).1 := by
  rcases scalar_cases M recs va with ⟨ha, hca⟩ | ⟨ha, hna⟩ <;>
    rcases scalar_cases M recs vb with ⟨hb, hcb⟩ | ⟨hb, hnb⟩
  · rw [hca, hcb, toVal_ordinal_date, toVal_ordinal_date]
    cases hx : (va.scalarOf.1.denote M).toScalar <;> cases hy : (vb.scalarOf.1.denote M).toScalar <;>
      simp [run_thrown, Agrees, holds_or, holds_not, holds_and, ha, hb, hx, hy, isDateOf_holds]
    rename_i x y
    unfold parseDate?
    cases hvx : isDateLabel x <;> cases hvy : isDateLabel y <;> simp [run_pure, run_thrown]
    simp [conc_mkBool, relT_ints M r _ _ _ _ (dayOf_denote M _ x hx hvx) (dayOf_denote M _ y hy hvy)]
  · rw [nonScalar_ordinal .date hnb]
    split <;> simp_all [run_thrown, Agrees, holds_or]
  · rw [nonScalar_ordinal .date hna]
    split <;> simp_all [run_thrown, Agrees, holds_or]
  · rw [nonScalar_ordinal .date hna]
    split <;> simp_all [run_thrown, Agrees, holds_or]

theorem conc_mkStr (M : Model) (recs : Records) (t : Term) :
    (SVal.scalar (.mkStr t)).conc M recs = .json (.str (t.denote M).toStr) := rfl

theorem addDays_op (M : Model) (recs : Records) (vd vn : SVal) (s : Trace) :
    Agrees M recs (.scalar (.mkStr (.dateLabel (.add (dayOf vd.scalarOf.1) (.intOf vn.scalarOf.1)))),
        .or vd.scalarOf.2 (.or vn.scalarOf.2 (.not (.and (isDateOf vd.scalarOf.1)
          (.and (.isInt vn.scalarOf.1) (inRangeT (.add (dayOf vd.scalarOf.1) (.intOf vn.scalarOf.1))))))))
      (run (match ordinal .date (vd.conc M recs), integer? (vn.conc M recs) with
        | some (days, _), some more =>
          match renderDate? (days + more) with
          | some label => pure (.json (.str label))
          | none => thrown
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
  rcases scalar_cases M recs vd with ⟨ha, hca⟩ | ⟨ha, hna⟩ <;>
    rcases scalar_cases M recs vn with ⟨hb, hcb⟩ | ⟨hb, hnb⟩
  · rw [hca, hcb, hsc, toVal_ordinal_date]
    cases hx : (vd.scalarOf.1.denote M).toScalar <;> cases hy : (vn.scalarOf.1.denote M).toScalar <;>
      simp [run_thrown, Agrees, holds_or, holds_not, holds_and, ha, hb, hx, hy, isDateOf_holds, holds_isInt]
    rename_i x n
    unfold parseDate?
    cases hv : isDateLabel x
    · simp [run_thrown]
    · have hz : (Term.add (dayOf vd.scalarOf.1) (.intOf vn.scalarOf.1)).denote M =
          .int (daysFromCivil (labelYear x) (labelMonth x) (labelDay x) + n) := by
        simp only [Term.denote, dayOf_denote M _ x hx hv, hy, Lit.toInt]
      simp only [Option.map_some, ite_true, Tazuna.Thm.Smt.Date.inRangeT_holds, hz, Lit.toInt]
      cases hr : renderDate? (daysFromCivil (labelYear x) (labelMonth x) (labelDay x) + n)
      · simp [run_thrown]
      · rename_i label
        have hd : (Term.dateLabel (.add (dayOf vd.scalarOf.1) (.intOf vn.scalarOf.1))).denote M = .str label := by
          show Lit.str ((renderDate? ((Term.add _ _).denote M).toInt).getD "") = _
          rw [hz]; simp [Lit.toInt, hr]
        simp [run_pure, conc_mkStr, hd, Lit.toStr]
  all_goals simp [hint vn, nonScalar_ordinal .date, run_thrown, Agrees, holds_or, *]

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
  | .json _ | .row .. | .single _ | .obj _ | .list _ | .bag _ | .emit .. => by
    simp [SVal.lookup, SVal.conc, run_thrown, Agrees, holds_tt]

theorem countIn_denote (M : Model) (recs : Records) : ∀ items : List (Term × SVal),
    (countIn items).denote M = .int (SVal.concItems M recs items).length
  | [] => rfl
  | (g, v) :: items => by
    simp only [countIn, Term.denote, countIn_denote M recs items, Lit.toInt, intLit]
    by_cases hg : g.holds M
    · simp only [Term.holds] at hg; simp [SVal.concItems, Term.holds, hg]; omega
    · simp only [Term.holds] at hg; simp [SVal.concItems, Term.holds, hg]

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
  | .bag items => by
    simp only [SVal.size, SVal.conc, run_pure]
    refine ⟨holds_ff M, ?_⟩
    simp only [conc_mkInt, countIn_denote M (r.conc M), Lit.toInt]
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

theorem any_same_items (M : Model) (recs : Records) (vv : SVal) : ∀ items : List (Term × SVal),
    (SVal.concItems M recs items).any (same · (vv.conc M recs)) = (SVal.includes vv (.bag items)).1.holds M
  | [] => rfl
  | (g, v) :: items => by
    have ih := any_same_items M recs vv items
    simp only [SVal.includes, List.map_cons, disj, List.foldr_cons] at ih ⊢
    rw [holds_or, holds_and, ← ih, same_conc M recs v vv]
    by_cases hg : g.holds M <;> simp [SVal.concItems, hg]

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
  | .bag items => by
    refine ⟨fun h => by simp [SVal.includes, holds_ff] at h, fun _ => ⟨_, rfl, any_same_items M recs vv items⟩⟩
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

/-! ### Collections: the values an operation visits, and a callback on each -/

theorem concItems_eq (M : Model) (recs : Records) : ∀ items : List (Term × SVal),
    SVal.concItems M recs items = (items.filter (·.1.holds M)).map (·.2.conc M recs)
  | [] => rfl
  | (g, v) :: items => by
    by_cases hg : g.holds M <;> simp [SVal.concItems, hg, concItems_eq M recs items]

theorem concItems_append (M : Model) (recs : Records) (xs ys : List (Term × SVal)) :
    SVal.concItems M recs (xs ++ ys) = SVal.concItems M recs xs ++ SVal.concItems M recs ys := by
  simp [concItems_eq]

theorem liveRows_heldKeys (M : Model) (e : String) (ss : List Slot) :
    (liveRows M e ss).filterMap (·.key) = (ss.filter (·.live.holds M)).map fun s => (s.key.denote M).toStr := by
  simp [liveRows, List.filterMap_map, Function.comp_def, Slot.row]

/-- A table's records as the semantics holds them: its live slots in slot order. -/
theorem heldKeys_conc (M : Model) (r : SRecords) (e : String) :
    heldKeys (r.conc M) e = ((r.slotsOf e).filter (·.live.holds M)).map fun s => (s.key.denote M).toStr := by
  simp only [heldKeys, SRecords.conc, List.filter_append, List.filterMap_append]
  have hs : ((r.singles.map fun (e, fields) => ({ entity := e, key := none, value := .obj (present M fields) } : Row)).filter
      (·.entity == e)).filterMap (·.key) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro row hrow
    simp only [List.mem_filter, List.mem_map] at hrow
    obtain ⟨⟨_, _, rfl⟩, _⟩ := hrow
    rfl
  rw [hs, List.append_nil, SRecords.slotsOf]
  induction r.keyed with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨e', slots⟩ := p
    simp only [List.flatMap_cons, List.filter_append, List.filterMap_append, List.filter_cons]
      at ih ⊢
    rw [ih]
    by_cases he : e' = e
    · subst he
      have h1 := liveRows_filter_self M e' slots
      have h2 := liveRows_heldKeys M e' slots
      simp only [liveRows] at h1 h2
      simp [h1, h2]
    · have := liveRows_filter_other M e e' he slots
      simp only [liveRows] at this
      simp [*]

theorem concItems_map_tt (M : Model) (recs : Records) (vs : List SVal) :
    SVal.concItems M recs (vs.map (tt, ·)) = SVal.concAll M recs vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [SVal.concItems, SVal.concAll, holds_tt, ih]

theorem concItems_guard (M : Model) (recs : Records) (c : Term) (xs : List (Term × SVal)) :
    SVal.concItems M recs (xs.map fun (g, v) => (.and c g, v)) =
      if c.holds M then SVal.concItems M recs xs else [] := by
  induction xs with
  | nil => split <;> rfl
  | cons x xs ih =>
    obtain ⟨g, v⟩ := x
    by_cases hc : c.holds M <;> simp_all [SVal.concItems, holds_and]

/-- What an operation visits in a collection that has items: their values, in order. -/
theorem items_elements (M : Model) (r : SRecords) (s : Trace) : ∀ (v : SVal) (items : List (Term × SVal)),
    v.items r = some items → (run (elements (v.conc M (r.conc M))) s).1 = .ok (SVal.concItems M (r.conc M) items)
  | .list vs, items, h => by
    cases h; simp [SVal.conc, elements, run_pure, concItems_map_tt]
  | .bag is, items, h => by cases h; simp [SVal.conc, elements, run_pure]
  | .table e, items, h => by
    cases h
    simp only [SVal.conc, elements]
    rw [run_note_pure, heldKeys_conc, concItems_eq]
    simp [List.filter_map, Function.comp_def, SVal.conc]
  | .ite c a b, items, h => by
    simp only [SVal.items, bind, Option.bind] at h
    cases ha : a.items r with
    | none => simp [ha] at h
    | some xs =>
      cases hb : b.items r with
      | none => simp [ha, hb] at h
      | some ys =>
        simp only [ha, hb, pure, Option.some.injEq] at h
        subst h
        rw [concItems_append, concItems_guard, concItems_guard, conc_ite]
        by_cases hc : c.holds M
        · simp [hc, holds_not, items_elements M r s a xs ha]
        · simp only [hc, Bool.false_eq_true, ite_false, holds_not, Bool.not_false, ite_true, List.nil_append]
          exact items_elements M r s b ys hb
  | .scalar _, _, h | .json _, _, h | .row .., _, h | .single _, _, h | .obj _, _, h | .emit .., _, h => by
    simp [SVal.items] at h

/-- That `x` throws exactly when `t` holds, and otherwise gives `b`. -/
def Yields {β : Type} (M : Model) (t : Term) (b : β) (x : Except Issue β) : Prop :=
  match x with
  | .error _ => t.holds M = true
  | .ok a => t.holds M = false ∧ a = b

/-- A callback's results on the visited values, from `mapM`: a throw when one throws, else each result in order. -/
theorem mapM_visits {β γ : Type} (M : Model) (recs : Records) (f : Val → EvalM β) (φ : γ → β) :
    ∀ (L : List (Term × SVal × Term × γ)),
      (∀ q ∈ L, q.1.holds M = true → ∀ s, Yields M q.2.2.1 (φ q.2.2.2) (run (f (q.2.1.conc M recs)) s).1) →
      ∀ s, Yields M (disj (L.map fun q => .and q.1 q.2.2.1)) ((L.filter (·.1.holds M)).map (φ ·.2.2.2))
        (run ((SVal.concItems M recs (L.map fun q => (q.1, q.2.1))).mapM f) s).1
  | [], _, s => by simp [SVal.concItems, run_pure, disj, holds_ff, Yields]
  | q :: L, h, s => by
    obtain ⟨g, v, e, y⟩ := q
    have ih := mapM_visits M recs f φ L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hg : g.holds M
    · have hc : SVal.concItems M recs ((g, v) :: L.map fun q => (q.1, q.2.1)) =
          v.conc M recs :: SVal.concItems M recs (L.map fun q => (q.1, q.2.1)) := by simp [SVal.concItems, hg]
      simp only [List.map_cons]
      rw [hc, List.mapM_cons, run_bind]
      have hq := h (g, v, e, y) List.mem_cons_self hg s
      rcases hr : run (f (v.conc M recs)) s with ⟨x, s1⟩
      rw [hr] at hq
      cases x with
      | error =>
        simp only [Yields] at hq ⊢
        simp [disj, holds_or, holds_and, hg, hq]
      | ok b =>
        simp only [Yields] at hq
        obtain ⟨he, rfl⟩ := hq
        dsimp only
        rw [run_bind]
        have ih1 := ih s1
        rcases hr2 : run ((SVal.concItems M recs (L.map fun q => (q.1, q.2.1))).mapM f) s1 with ⟨x2, s2⟩
        rw [hr2] at ih1
        try rw [hr2]
        cases x2 with
        | error =>
          simp only [Yields] at ih1 ⊢
          simp only [disj, List.foldr_cons, holds_or, holds_and, hg, he, Bool.true_and, Bool.false_or] at ih1 ⊢
          exact ih1
        | ok bs =>
          simp only [Yields] at ih1 ⊢
          obtain ⟨h1, h2⟩ := ih1
          simp only [run_pure]
          refine ⟨?_, by simp [hg, h2]⟩
          simp only [disj, List.foldr_cons, holds_or, holds_and, hg, he, Bool.true_and, Bool.false_or] at h1 ⊢
          exact h1
    · have hc : SVal.concItems M recs ((g, v) :: L.map fun q => (q.1, q.2.1)) =
          SVal.concItems M recs (L.map fun q => (q.1, q.2.1)) := by simp [SVal.concItems, hg]
      simp only [List.map_cons]
      rw [hc]
      have ih1 := ih s
      rcases hr : run ((SVal.concItems M recs (L.map fun q => (q.1, q.2.1))).mapM f) s with ⟨x, s1⟩
      rw [hr] at ih1
      try rw [hr]
      have hd : (disj ((g.and e) :: L.map fun q => .and q.1 q.2.2.1)).holds M =
          (disj (L.map fun q => .and q.1 q.2.2.1)).holds M := by
        simp [disj, holds_or, holds_and, hg]
      cases x with
      | error => simp only [Yields] at ih1 ⊢; rw [hd]; exact ih1
      | ok bs =>
        simp only [Yields] at ih1 ⊢
        obtain ⟨h1, h2⟩ := ih1
        exact ⟨by rw [hd]; exact h1, by simp [hg, h2]⟩

/-- The visits that a callback method's encoding makes: each item with the callback's encoding on its value. -/
theorem visits_ok (env : SEnv) (vars : List (String × SVal)) (x : String) (body : Expr)
    (F : Term × SVal → Except String Visit)
    (hF : ∀ i q, F i = .ok q → q.1 = i.1 ∧ q.2.1 = i.2 ∧ seval env ((x, i.2) :: vars) body = .ok q.2.2) :
    ∀ (items : List (Term × SVal)) (visits : List Visit), items.mapM F = .ok visits →
      visits.map (fun q => (q.1, q.2.1)) = items ∧ ∀ q ∈ visits, seval env ((x, q.2.1) :: vars) body = .ok q.2.2
  | [], visits, h => by cases h; exact ⟨rfl, by simp⟩
  | i :: items, visits, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · contradiction
    rename_i q hq
    split at h
    · contradiction
    rename_i rest hrest
    cases h
    obtain ⟨h1, h2⟩ := visits_ok env vars x body F hF items rest hrest
    obtain ⟨e1, e2, e3⟩ := hF i q hq
    refine ⟨by simp [h1, e1, e2], ?_⟩
    intro q' hq'
    simp only [List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · rw [e2]; exact e3
    · exact h2 q' hq'

/-- A callback method's evaluation: the collection, the values it visits, the callback on each, then `k` on the results. -/
theorem visits_op {β γ : Type} {M : Model} {r : SRecords} {x : EvalM Val} {vc : SVal} {ec : Term}
    {items : List (Term × SVal)} {f : Val → EvalM β} {φ : γ → β} {L : List (Term × SVal × Term × γ)}
    {k : List β → EvalM Val} {res : SRes}
    (hx : ∀ s, Agrees M (r.conc M) (vc, ec) (run x s).1)
    (hi : vc.items r = some items)
    (hL : L.map (fun q => (q.1, q.2.1)) = items)
    (hf : ∀ q ∈ L, q.1.holds M = true → ∀ s, Yields M q.2.2.1 (φ q.2.2.2) (run (f (q.2.1.conc M (r.conc M))) s).1)
    (herr : ec.holds M = true ∨ (disj (L.map fun q => .and q.1 q.2.2.1)).holds M = true → res.2.holds M = true)
    (hk : ec.holds M = false → (disj (L.map fun q => .and q.1 q.2.2.1)).holds M = false →
      ∀ s, Agrees M (r.conc M) res (run (k ((L.filter (·.1.holds M)).map (φ ·.2.2.2))) s).1)
    (s : Trace) :
    Agrees M (r.conc M) res (run (x >>= fun v => elements v >>= fun vs => vs.mapM f >>= k) s).1 := by
  refine agrees_bind (P := Agrees M _ res) hx (fun h _ => herr (.inl h)) ?_ s
  intro s1 h1
  rw [run_bind]
  rcases hr : run (elements (vc.conc M (r.conc M))) s1 with ⟨y, s2⟩
  have he := items_elements M r s1 vc items hi
  rw [hr] at he
  obtain rfl : y = _ := he
  try rw [hr]
  dsimp only
  rw [run_bind]
  have hm := mapM_visits M (r.conc M) f φ L hf s2
  rw [hL] at hm
  rcases hr2 : run (List.mapM f (SVal.concItems M (r.conc M) items)) s2 with ⟨z, s3⟩
  rw [hr2] at hm
  try rw [hr2]
  cases z with
  | error => simp only [Yields] at hm; exact herr (.inr hm)
  | ok bs => simp only [Yields] at hm; obtain ⟨h2, rfl⟩ := hm; exact hk h1 h2 s3

/-- An evaluation followed by a pure step yields that step on the value its encoding agrees on. -/
theorem yields_pure {β : Type} {M : Model} {recs : Records} {y : EvalM Val} {rb : SRes} (g : Val → β)
    (h : ∀ s, Agrees M recs rb (run y s).1) (s : Trace) :
    Yields M rb.2 (g (rb.1.conc M recs)) (run (y >>= fun w => pure (g w)) s).1 := by
  rw [run_bind]
  have := h s
  rcases hr : run y s with ⟨x, s1⟩
  rw [hr] at this
  try rw [hr]
  cases x with
  | error => exact this
  | ok w => obtain ⟨h1, rfl⟩ := this; exact ⟨h1, rfl⟩

/-- The callback's results on visits as `mapM_visits` takes them: each with its visit. -/
abbrev visited (visits : List Visit) : List (Term × SVal × Term × Visit) := visits.map fun q => (q.1, q.2.1, q.2.2.2, q)

theorem thrownIn_eq (visits : List Visit) :
    thrownIn visits = disj ((visited visits).map fun q => .and q.1 q.2.2.1) := by
  simp [thrownIn, List.map_map, Function.comp_def]

theorem filter_kept (M : Model) (recs : Records) : ∀ visits : List Visit,
    (((visits.filter (·.1.holds M)).map fun q => (q.2.1.conc M recs, q.2.2.1.truthy.holds M)).filterMap
        fun (v, kept) => if kept then some v else none) =
      SVal.concItems M recs (visits.map fun q => (.and q.1 q.2.2.1.truthy, q.2.1))
  | [] => rfl
  | (g, v, b, e) :: visits => by
    have ih := filter_kept M recs visits
    by_cases hg : g.holds M <;> by_cases ht : b.truthy.holds M <;>
      simp [SVal.concItems, holds_and, hg, ht, ih]

theorem disj_cons (a : Term) (l : List Term) : disj (a :: l) = .or a (disj l) := rfl

theorem yields_of_agrees {M : Model} {recs : Records} {r : SRes} {x : Except Issue Val} (h : Agrees M recs r x) :
    Yields M r.2 (r.1.conc M recs) x := by
  cases x with
  | error => exact h
  | ok v => exact h

theorem any_visits (M : Model) (recs : Records) (P : SVal → Term) (p : Val → Bool)
    (hP : ∀ b, (P b).holds M = p (b.conc M recs)) : ∀ visits : List Visit,
    ((visits.filter (·.1.holds M)).map (·.2.2.1.conc M recs)).any p =
      (disj (visits.map fun q => .and q.1 (P q.2.2.1))).holds M
  | [] => rfl
  | (g, v, b, e) :: visits => by
    have ih := any_visits M recs P p hP visits
    rw [List.map_cons, disj_cons, holds_or, holds_and, ← ih]
    by_cases hg : g.holds M <;> simp [hg, hP]

theorem map_visits (M : Model) (recs : Records) (visits : List Visit) :
    (visits.filter (·.1.holds M)).map (·.2.2.1.conc M recs) =
      SVal.concItems M recs (visits.map fun q => (q.1, q.2.2.1)) := by
  simp [concItems_eq, List.filter_map, Function.comp_def]

/-! ### only, sum, min and max on the visited values -/

theorem disj_guards (M : Model) (recs : Records) : ∀ items : List (Term × SVal),
    (disj (items.map (·.1))).holds M = decide (1 ≤ (SVal.concItems M recs items).length)
  | [] => rfl
  | (g, v) :: items => by
    rw [List.map_cons, disj_cons, holds_or, disj_guards M recs items]
    by_cases hg : g.holds M <;> simp [SVal.concItems, hg]

theorem twoIn_holds (M : Model) (recs : Records) : ∀ items : List (Term × SVal),
    (twoIn items).holds M = decide (2 ≤ (SVal.concItems M recs items).length)
  | [] => rfl
  | (g, v) :: items => by
    rw [twoIn, holds_or, holds_and, disj_guards M recs items, twoIn_holds M recs items]
    by_cases hg : g.holds M <;> simp [SVal.concItems, hg]
    omega

theorem firstIn_conc (M : Model) (recs : Records) : ∀ items : List (Term × SVal),
    (firstIn items).conc M recs = ((SVal.concItems M recs items).head?).getD .undef
  | [] => rfl
  | (g, v) :: items => by
    rw [firstIn, conc_ite, firstIn_conc M recs items]
    by_cases hg : g.holds M <;> simp [SVal.concItems, hg]

theorem safe_iff (x : Int) : (decide (-2 ^ 53 < x) && decide (x < 2 ^ 53)) = decide (x.natAbs < 2 ^ 53) := by
  rw [← Bool.decide_and]
  exact decide_eq_decide.mpr (by omega)

theorem safeT_holds (M : Model) (t : Term) :
    (safeT t).holds M = decide ((t.denote M).toInt.natAbs < 2 ^ 53) := by
  simp only [safeT, Term.holds, Term.denote, Lit.toBool, intLit, Lit.toInt]
  exact safe_iff _

/-- What `safeInteger?` takes of a value that an encoding agrees on: its integer, when the term of a bad key fails. -/
theorem safeInteger_conc (M : Model) (recs : Records) (b : SVal) :
    safeInteger? (b.conc M recs) =
      if (Term.or b.scalarOf.2 (.not (.and (.isInt b.scalarOf.1) (safeT (.intOf b.scalarOf.1))))).holds M then none
      else some ((Term.intOf b.scalarOf.1).denote M).toInt := by
  rcases scalar_cases M recs b with ⟨h, hc⟩ | ⟨h, hn⟩
  · rw [hc]
    cases hx : (b.scalarOf.1.denote M).toScalar <;>
      simp [Scalar.toVal, Scalar.toValue?, Val.ofOption, safeInteger?, holds_or, holds_not, holds_and, h, holds_isInt,
        hx, safeT_holds, denote_intOf]
    rename_i n
    by_cases hn : n.natAbs < 2 ^ 53 <;> simp [hn]
  · have : safeInteger? (b.conc M recs) = none := by
      revert hn; cases b.conc M recs with
      | json j => cases j <;> simp [NonScalar, safeInteger?]
      | _ => simp [NonScalar, safeInteger?]
    rw [this]; simp [holds_or, h]

theorem sum_visits (M : Model) (recs : Records) : ∀ (visits : List Visit) (a : Int),
    match ((visits.filter (·.1.holds M)).map (·.2.2.1.conc M recs)).mapM safeInteger? with
    | none => (sumIn visits).2.holds M = true
    | some ints => (sumIn visits).2.holds M = false ∧ ints.foldl (· + ·) a = a + ((sumIn visits).1.denote M).toInt
  | [], a => by simp [sumIn, holds_ff, intLit, Term.denote, Lit.toInt]
  | (g, v, b, e) :: visits, a => by
    by_cases hg : g.holds M
    · simp only [List.filter_cons, hg, ite_true, List.map_cons, List.mapM_cons, safeInteger_conc]
      by_cases hb : (Term.or b.scalarOf.2 (.not (.and (.isInt b.scalarOf.1) (safeT (.intOf b.scalarOf.1))))).holds M
      · simp only [hb, ite_true]
        simp [sumIn, holds_or, holds_and, hg, hb]
      · simp only [hb, Bool.false_eq_true, ite_false]
        have ih := sum_visits M recs visits (a + ((Term.intOf b.scalarOf.1).denote M).toInt)
        revert ih
        cases hm : ((visits.filter (·.1.holds M)).map (·.2.2.1.conc M recs)).mapM safeInteger? with
        | none => intro ih; simp [sumIn, holds_or, holds_and, hg, ih]
        | some ints =>
          intro ih
          obtain ⟨h1, h2⟩ := ih
          refine ⟨by simp only [sumIn, holds_or, holds_and, hg, h1] at hb ⊢; simpa using hb, ?_⟩
          simp only [List.foldl_cons, h2, sumIn, Term.denote, Lit.toInt, Term.holds] at *
          simp only [hg, ite_true]
          omega
    · simp only [List.filter_cons, hg, Bool.false_eq_true, ite_false]
      have ih := sum_visits M recs visits a
      revert ih
      cases ((visits.filter (·.1.holds M)).map (·.2.2.1.conc M recs)).mapM safeInteger? with
      | none => intro ih; simp [sumIn, holds_or, holds_and, hg, ih]
      | some ints =>
        intro ih
        obtain ⟨h1, h2⟩ := ih
        refine ⟨by simp [sumIn, holds_or, holds_and, hg, h1], ?_⟩
        rw [h2]
        simp only [Term.holds] at hg
        simp [sumIn, Term.denote, hg, intLit, Lit.toInt]

/-- A key that a min or max is building: none before the first value, else the least key so far and its value. -/
def accStep (lt : Int × Nat → Int × Nat → Bool) (acc : Option (Val × (Int × Nat))) (k : Val × (Int × Nat)) :
    Option (Val × (Int × Nat)) :=
  some (match acc with
    | none => k
    | some m => if lt k.2 m.2 then k else m)

theorem foldl_accStep (lt : Int × Nat → Int × Nat → Bool) : ∀ (ks : List (Val × (Int × Nat))) (k : Val × (Int × Nat)),
    ks.foldl (accStep lt) (some k) = some (ks.foldl (fun m k => if lt k.2 m.2 then k else m) k)
  | [], _ => rfl
  | k' :: ks, k => by simp only [List.foldl_cons, accStep]; exact foldl_accStep lt ks _

theorem least_eq (lt : Int × Nat → Int × Nat → Bool) (l : List (Val × (Int × Nat))) :
    least lt l = ((l.foldl (accStep lt) none).map (·.1)).getD .undef := by
  cases l with
  | nil => rfl
  | cons k ks => simp only [least, List.foldl_cons, accStep, foldl_accStep]; rfl

/-- What ordinal reads of a scalar term as a key of `order`: the key that keyT gives, when keyOkT holds. -/
theorem key_ordinal (M : Model) (order : Order) (t : Term) :
    ordinal order ((t.denote M).toScalar.toVal) =
      if (keyOkT order t).holds M then some (((keyT order t).denote M).toInt, 0) else none := by
  cases order
  · rw [toVal_ordinal]
    cases hx : (t.denote M).toScalar <;> simp [keyOkT, keyT, holds_isInt, hx, denote_intOf]
  · rw [toVal_ordinal_date]
    simp only [keyOkT, keyT, isDateOf_holds]
    cases hx : (t.denote M).toScalar <;> simp only [Bool.false_eq_true, ite_false]
    rename_i x
    unfold parseDate?
    by_cases hv : isDateLabel x = true
    · simp [hv, dayOf_denote M t x hx hv, Lit.toInt]
    · simp [hv]

/-- The key that keyT gives is an integer term where keyOkT holds. -/
theorem keyT_int (M : Model) (order : Order) (t : Term) (h : (keyOkT order t).holds M = true) :
    (keyT order t).denote M = .int ((keyT order t).denote M).toInt := by
  cases order
  · rfl
  · simp only [keyOkT, isDateOf_holds] at h
    cases hx : (t.denote M).toScalar <;> simp only [hx, Bool.false_eq_true] at h
    rename_i x
    simp [keyT, dayOf_denote M t x hx h, Lit.toInt]

theorem keyT_ite (M : Model) (order : Order) (c a b : Term) :
    (keyT order (.ite c a b)).denote M = if c.holds M then (keyT order a).denote M else (keyT order b).denote M := by
  cases order
  · by_cases hc : (c.denote M).toBool <;> simp [keyT, Term.denote, Term.holds, hc]
  · simp only [keyT, dayOf, Term.denote]

/-- That a min's or max's terms `found` and `m` stand for the key `acc` so far, a key of `order`. -/
def LeastRel (M : Model) (order : Order) (acc : Option (Val × (Int × Nat))) (found m : Term) : Prop :=
  match acc with
  | none => found.holds M = false ∧ (m.denote M).toScalar = .undef
  | some (kv, kk) =>
    found.holds M = true ∧ (m.denote M).toScalar.toVal = kv ∧ (keyT order m).denote M = .int kk.1 ∧ kk.2 = 0

theorem leastIn_conc (M : Model) (recs : Records) (order : Order) (lt : Term → Term → Term)
    (plt : Int × Nat → Int × Nat → Bool)
    (hlt : ∀ a b : Term, ∀ x y : Int, (keyT order a).denote M = .int x → (keyT order b).denote M = .int y →
      (lt a b).holds M = plt (x, 0) (y, 0)) :
    ∀ (visits : List Visit) (acc : Option (Val × (Int × Nat))) (found m : Term),
      (keysBad order visits).holds M = false → LeastRel M order acc found m →
      ((leastIn lt found m visits).denote M).toScalar.toVal =
        ((((visits.filter (·.1.holds M)).map fun q =>
          (q.2.2.1.conc M recs, (((keyT order q.2.2.1.scalarOf.1).denote M).toInt, 0))).foldl (accStep plt) acc).map
          (·.1)).getD .undef
  | [], acc, found, m, _, hr => by
    simp only [leastIn, List.filter_nil, List.map_nil, List.foldl_nil]
    cases acc with
    | none => obtain ⟨_, hm⟩ := hr; simp [hm, Scalar.toVal, Scalar.toValue?, Val.ofOption]
    | some a =>
      obtain ⟨kv, kk⟩ := a
      obtain ⟨_, hm, _, _⟩ := hr
      simp [hm]
  | (g, v, b, e) :: visits, acc, found, m, hbad, hr => by
    simp only [keysBad, List.map_cons, disj_cons, holds_or, Bool.or_eq_false_iff] at hbad
    obtain ⟨hb, hrest⟩ := hbad
    simp only [leastIn]
    by_cases hg : g.holds M
    · simp only [holds_and, hg, Bool.true_and, holds_or, holds_not, Bool.or_eq_false_iff, Bool.not_eq_false'] at hb
      obtain ⟨hs, hi⟩ := hb
      rcases scalar_cases M recs b with ⟨_, hc⟩ | ⟨h, _⟩
      · have hk := keyT_int M order b.scalarOf.1 hi
        generalize hn : ((keyT order b.scalarOf.1).denote M).toInt = n at hk
        simp only [List.filter_cons, hg, ite_true, List.map_cons, List.foldl_cons]
        refine leastIn_conc M recs order lt plt hlt visits _ _ _ (by simpa [keysBad] using hrest) ?_
        rw [hc, hn]
        cases acc with
        | none =>
          obtain ⟨hf, _⟩ := hr
          have hcond : (Term.and g (.or (.not found) (lt b.scalarOf.1 m))).holds M = true := by
            simp [holds_and, holds_or, holds_not, hg, hf]
          refine ⟨by simp [holds_or, hg], ?_, ?_, by simp⟩
          · rw [denote_ite, hcond]; rfl
          · rw [keyT_ite, hcond]; exact hk
        | some a =>
          obtain ⟨kv, kk⟩ := a
          obtain ⟨hf, hm, hmk, hk0⟩ := hr
          obtain ⟨mn, k0⟩ := kk
          simp only at hmk hk0
          subst hk0
          have hl := hlt b.scalarOf.1 m n mn hk hmk
          simp only [LeastRel, accStep]
          by_cases hc' : plt (n, 0) (mn, 0)
          · have hcond : (Term.and g (.or (.not found) (lt b.scalarOf.1 m))).holds M = true := by
              simp [holds_and, holds_or, holds_not, hg, hl, hc']
            simp only [hc', ite_true]
            refine ⟨by simp [holds_or, hf], ?_, ?_, by simp⟩
            · rw [denote_ite, hcond]; rfl
            · rw [keyT_ite, hcond]; exact hk
          · have hcond : (Term.and g (.or (.not found) (lt b.scalarOf.1 m))).holds M = false := by
              simp [holds_and, holds_or, holds_not, hg, hf, hl, hc']
            simp only [hc', Bool.false_eq_true, ite_false]
            refine ⟨by simp [holds_or, hf], ?_, ?_, by simp⟩
            · rw [denote_ite, hcond]; exact hm
            · rw [keyT_ite, hcond]; exact hmk
      · simp [h] at hs
    · simp only [List.filter_cons, hg, Bool.false_eq_true, ite_false]
      have hcond : (Term.and g (.or (.not found) (lt b.scalarOf.1 m))).holds M = false := by simp [holds_and, hg]
      refine leastIn_conc M recs order lt plt hlt visits acc _ _ (by simpa [keysBad] using hrest) ?_
      cases acc with
      | none =>
        obtain ⟨hf, hm⟩ := hr
        exact ⟨by simp [holds_or, hf, hg], by rw [denote_ite, hcond]; exact hm⟩
      | some a =>
        obtain ⟨kv, kk⟩ := a
        obtain ⟨hf, hm, hmk, hk0⟩ := hr
        exact ⟨by simp [holds_or, hf], by rw [denote_ite, hcond]; exact hm, by rw [keyT_ite, hcond]; exact hmk, hk0⟩

theorem keyOf_conc (M : Model) (recs : Records) (order : Order) (b : SVal) :
    Ir.keyOf order (b.conc M recs) =
      if (Term.or b.scalarOf.2 (.not (keyOkT order b.scalarOf.1))).holds M then thrown
      else pure (((keyT order b.scalarOf.1).denote M).toInt, 0) := by
  rcases scalar_cases M recs b with ⟨h, hc⟩ | ⟨h, hn⟩
  · rw [hc]
    simp only [Ir.keyOf, key_ordinal, holds_or, holds_not, h, Bool.false_or]
    cases (keyOkT order b.scalarOf.1).holds M <;> rfl
  · simp [Ir.keyOf, nonScalar_ordinal order hn, holds_or, h]

theorem disj_split (M : Model) (B : Visit → Term) : ∀ visits : List Visit,
    (disj (visits.map fun q => .and q.1 (.or q.2.2.2 (B q)))).holds M =
      ((thrownIn visits).holds M || (disj (visits.map fun q => .and q.1 (B q))).holds M)
  | [] => rfl
  | q :: visits => by
    have ih := disj_split M B visits
    simp only [thrownIn] at ih ⊢
    rw [List.map_cons, List.map_cons, List.map_cons, disj_cons, disj_cons, disj_cons, holds_or, holds_or, holds_or, ih]
    simp only [holds_and, holds_or]
    cases q.1.holds M <;> cases q.2.2.2.holds M <;> cases (B q).holds M <;> simp

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
  | vars, .addDays d n, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i ra hra
    split at h
    · contradiction
    rename_i rb hrb
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars d ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    rw [run_bind]
    have h2 := seval_agrees M env fields vars n rb hrb s1
    rcases hr : run (eval (concEnv M env fields) (concVars M (env.records.conc M) vars) n) s1 with ⟨y, s2⟩
    rw [hr] at h2
    cases y with
    | error =>
      have he : rb.2.holds M = true := h2
      simp [Agrees, holds_or, he]
    | ok w =>
      obtain ⟨h2, rfl⟩ := h2
      exact agrees_err (by simp [holds_or, h1, h2]) (addDays_op M _ ra.1 rb.1 s2)
  | vars, .compare rel .date a b, r, h, s => by
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
    exact agrees_err (by simp [holds_or, h1, h2]) (dateCompare_op M _ rel ra.1 rb.1 s2)
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
    · split at h
      case h_2 => contradiction
      rename_i xs ys hxs hys
      cases h
      simp only [eval]
      refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars a ra hra) (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
      intro s1 h1
      refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars b rb hrb)
        (fun h2 e => by simp [Agrees, holds_or, h2]) ?_ s1
      intro s2 h2
      rw [run_bind]
      rcases hr : run (elements (ra.1.conc M (env.records.conc M))) s2 with ⟨y, s3⟩
      have he := items_elements M env.records s2 ra.1 xs hxs
      rw [hr] at he
      obtain rfl : y = _ := he
      try rw [hr]
      dsimp only
      rw [run_bind]
      rcases hr2 : run (elements (rb.1.conc M (env.records.conc M))) s3 with ⟨z, s4⟩
      have he2 := items_elements M env.records s3 rb.1 ys hys
      rw [hr2] at he2
      obtain rfl : z = _ := he2
      try rw [hr2]
      exact ⟨by simp [holds_or, h1, h2], by simp [SVal.conc, concItems_append]⟩
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
  | vars, .filter _ c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visited visits) (φ := fun q => (q.2.1.conc M (env.records.conc M), q.2.2.1.truthy.holds M))
      (by simp [visited, List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      have := yields_pure (fun w => (q.2.1.conc M (env.records.conc M), truthy w))
        (seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq)) s1
      rw [truthy_conc M (env.records.conc M)]
      exact this
    · intro he
      rw [← thrownIn_eq visits] at he
      simp only [holds_or]
      rcases he with he | he <;> simp [he]
    · intro h1 h2 s1
      rw [← thrownIn_eq visits] at h2
      simp only [run_pure, List.filter_map, Function.comp_def, List.map_map]
      refine ⟨by simp [holds_or, h1, h2], ?_⟩
      simp only [SVal.conc]
      rw [← filter_kept]
  | vars, .map _ c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visited visits) (φ := fun q => q.2.2.1.conc M (env.records.conc M))
      (by simp [visited, List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [visited, List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      exact yields_of_agrees (seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq) s1)
    · intro he
      rw [← thrownIn_eq visits] at he
      simp only [holds_or]
      rcases he with he | he <;> simp [he]
    · intro h1 h2 s1
      rw [← thrownIn_eq visits] at h2
      refine ⟨by simp [holds_or, h1, h2], ?_⟩
      simp only [SVal.conc, visited, List.filter_map, Function.comp_def, List.map_map, ← map_visits]
  | vars, .some .bag c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visited visits) (φ := fun q => q.2.2.1.conc M (env.records.conc M))
      (by simp [visited, List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [visited, List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      exact yields_of_agrees (seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq) s1)
    · intro he
      rw [← thrownIn_eq visits] at he
      simp only [holds_or]
      rcases he with he | he <;> simp [he]
    · intro h1 h2 s1
      rw [← thrownIn_eq visits] at h2
      refine ⟨by simp [holds_or, h1, h2], ?_⟩
      rw [conc_mkBool, ← any_visits M (env.records.conc M) (·.same trueT) (same · (.json (.bool true)))
        (fun b => by rw [same_conc M (env.records.conc M)]; rfl)]
      simp [visited, List.filter_map, Function.comp_def]
  | vars, .every .bag c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visited visits) (φ := fun q => q.2.2.1.conc M (env.records.conc M))
      (by simp [visited, List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [visited, List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      exact yields_of_agrees (seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq) s1)
    · intro he
      rw [← thrownIn_eq visits] at he
      simp only [holds_or]
      rcases he with he | he <;> simp [he]
    · intro h1 h2 s1
      rw [← thrownIn_eq visits] at h2
      refine ⟨by simp [holds_or, h1, h2], ?_⟩
      rw [conc_mkBool, holds_not, ← any_visits M (env.records.conc M) (·.same falseT) (same · (.json (.bool false)))
        (fun b => by rw [same_conc M (env.records.conc M)]; rfl)]
      simp [visited, List.filter_map, Function.comp_def]
  | vars, .some .array .., r, h, s | vars, .every .array .., r, h, s
  | vars, .sortedBy .., r, h, s
  | vars, .createKey _, r, h, s => by simp [seval] at h
  | vars, .sum c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visited visits) (φ := fun q => q.2.2.1.conc M (env.records.conc M))
      (by simp [visited, List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [visited, List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      exact yields_of_agrees (seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq) s1)
    · intro he
      rw [← thrownIn_eq visits] at he
      simp only [holds_or]
      rcases he with he | he <;> simp [he]
    · intro h1 h2 s1
      rw [← thrownIn_eq visits] at h2
      have hns : ((visited visits).filter (·.1.holds M)).map (fun q => q.2.2.2.2.2.1.conc M (env.records.conc M)) =
          (visits.filter (·.1.holds M)).map (·.2.2.1.conc M (env.records.conc M)) := by
        simp [visited, List.filter_map, Function.comp_def]
      rw [hns]
      have hs := sum_visits M (env.records.conc M) visits 0
      revert hs
      cases hm : ((visits.filter (·.1.holds M)).map (·.2.2.1.conc M (env.records.conc M))).mapM safeInteger? with
      | none =>
        intro hs
        simp only at hs
        show (Term.or _ _).holds M = true
        simp [holds_or, hs]
      | some ints =>
        intro hs
        obtain ⟨hb1, hb2⟩ := hs
        dsimp only
        rw [hb2, Int.zero_add]
        by_cases ht : (((sumIn visits).1).denote M).toInt.natAbs < 2 ^ 53
        · simp only [ht, ite_true, run_pure]
          refine ⟨by simp [holds_or, holds_not, h1, h2, hb1, safeT_holds, ht], ?_⟩
          simp [conc_mkInt, Lean.JsonNumber.fromInt]
        · simp only [ht, ite_false]
          show (Term.or _ _).holds M = true
          simp [holds_or, holds_not, safeT_holds, ht]
  | vars, .min order c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visits.map fun q => (q.1, q.2.1, .or q.2.2.2 (.or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1))), q))
      (φ := fun q => (q.2.2.1.conc M (env.records.conc M), (((keyT order q.2.2.1.scalarOf.1).denote M).toInt, 0)))
      (by simp [List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      have hb' : Agrees M (env.records.conc M) q.2.2 (run (eval (concEnv M env fields)
          ((x, q.2.1.conc M (env.records.conc M)) :: concVars M (env.records.conc M) vars) body) s1).1 :=
        seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq) s1
      rw [run_bind]
      rcases hr : run (eval (concEnv M env fields)
          ((x, q.2.1.conc M (env.records.conc M)) :: concVars M (env.records.conc M) vars) body) s1 with ⟨y, s2⟩
      rw [hr] at hb'
      try rw [hr]
      cases y with
      | error =>
        have he : q.2.2.2.holds M = true := hb'
        simp only [Yields]; simp [holds_or, he]
      | ok w =>
        obtain ⟨he, rfl⟩ := hb'
        dsimp only
        rw [run_bind, keyOf_conc M _ order]
        by_cases hk : (Term.or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1))).holds M
        · simp only [hk, ite_true, run_thrown, Yields]; simp [holds_or, hk]
        · simp only [hk, Bool.false_eq_true, ite_false, run_pure, Yields]
          refine ⟨?_, ?_⟩ <;> simp_all [holds_or]
    · intro he
      rw [List.map_map] at he
      simp only [Function.comp_def] at he
      rw [disj_split M (fun q => .or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1)))] at he
      simp only [holds_or, keysBad]
      rcases he with he | he <;> simp_all
    · intro h1 h2 s1
      rw [List.map_map] at h2
      simp only [Function.comp_def] at h2
      rw [disj_split M (fun q => .or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1)))] at h2
      simp only [Bool.or_eq_false_iff] at h2
      obtain ⟨h2, h3⟩ := h2
      simp only [run_pure]
      refine ⟨by simp [holds_or, keysBad, h1, h2, h3], ?_⟩
      rw [least_eq, conc_scalar, leastIn_conc M (env.records.conc M) order _ keyLt ?_ visits none ff undefT
        (by simpa [keysBad] using h3) ⟨holds_ff M, rfl⟩]
      · simp [List.filter_map, Function.comp_def]
      · intro a b x y ha hb
        simp [keyLt, Term.holds, Term.denote, Lit.toBool, Lit.toInt, ha, hb]
  | vars, .max order c x body, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    split at h
    · contradiction
    rename_i visits hvisits
    cases h
    obtain ⟨hL, hb⟩ := visits_ok env vars x body _ (fun i q hq => by
      split at hq
      · contradiction
      · rename_i v hv; cases hq; exact ⟨rfl, rfl, hv⟩) items visits hvisits
    simp only [eval]
    refine visits_op (hx := seval_agrees M env fields vars c rc hrc) (hi := hitems)
      (L := visits.map fun q => (q.1, q.2.1, .or q.2.2.2 (.or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1))), q))
      (φ := fun q => (q.2.2.1.conc M (env.records.conc M), (((keyT order q.2.2.1.scalarOf.1).denote M).toInt, 0)))
      (by simp [List.map_map, Function.comp_def, ← hL]) ?_ ?_ ?_ s
    · intro q hq _ s1
      simp only [List.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      have hb' : Agrees M (env.records.conc M) q.2.2 (run (eval (concEnv M env fields)
          ((x, q.2.1.conc M (env.records.conc M)) :: concVars M (env.records.conc M) vars) body) s1).1 :=
        seval_agrees M env fields ((x, q.2.1) :: vars) body q.2.2 (hb q hq) s1
      rw [run_bind]
      rcases hr : run (eval (concEnv M env fields)
          ((x, q.2.1.conc M (env.records.conc M)) :: concVars M (env.records.conc M) vars) body) s1 with ⟨y, s2⟩
      rw [hr] at hb'
      try rw [hr]
      cases y with
      | error =>
        have he : q.2.2.2.holds M = true := hb'
        simp only [Yields]; simp [holds_or, he]
      | ok w =>
        obtain ⟨he, rfl⟩ := hb'
        dsimp only
        rw [run_bind, keyOf_conc M _ order]
        by_cases hk : (Term.or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1))).holds M
        · simp only [hk, ite_true, run_thrown, Yields]; simp [holds_or, hk]
        · simp only [hk, Bool.false_eq_true, ite_false, run_pure, Yields]
          refine ⟨?_, ?_⟩ <;> simp_all [holds_or]
    · intro he
      rw [List.map_map] at he
      simp only [Function.comp_def] at he
      rw [disj_split M (fun q => .or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1)))] at he
      simp only [holds_or, keysBad]
      rcases he with he | he <;> simp_all
    · intro h1 h2 s1
      rw [List.map_map] at h2
      simp only [Function.comp_def] at h2
      rw [disj_split M (fun q => .or q.2.2.1.scalarOf.2 (.not (keyOkT order q.2.2.1.scalarOf.1)))] at h2
      simp only [Bool.or_eq_false_iff] at h2
      obtain ⟨h2, h3⟩ := h2
      simp only [run_pure]
      refine ⟨by simp [holds_or, keysBad, h1, h2, h3], ?_⟩
      rw [least_eq, conc_scalar, leastIn_conc M (env.records.conc M) order _ (fun a b => keyLt b a) ?_ visits none ff undefT
        (by simpa [keysBad] using h3) ⟨holds_ff M, rfl⟩]
      · simp [List.filter_map, Function.comp_def]
      · intro a b x y ha hb
        simp [keyLt, Term.holds, Term.denote, Lit.toBool, Lit.toInt, ha, hb]
  | vars, .only c, r, h, s => by
    simp only [seval, bind, Except.bind] at h
    split at h
    · contradiction
    rename_i rc hrc
    split at h
    case h_2 => contradiction
    rename_i items hitems
    cases h
    simp only [eval]
    refine agrees_bind (P := Agrees M _ _) (seval_agrees M env fields vars c rc hrc)
      (fun h1 _ => by simp [Agrees, holds_or, h1]) ?_ s
    intro s1 h1
    rw [run_bind]
    rcases hr : run (elements (rc.1.conc M (env.records.conc M))) s1 with ⟨y, s2⟩
    have he := items_elements M env.records s1 rc.1 items hitems
    rw [hr] at he
    obtain rfl : y = _ := he
    try rw [hr]
    dsimp only
    have h2 := twoIn_holds M (env.records.conc M) items
    have h3 := firstIn_conc M (env.records.conc M) items
    revert h2 h3
    cases SVal.concItems M (env.records.conc M) items with
    | nil => intro h2 h3; exact ⟨by simp [holds_or, h1, h2], by simp [h3]⟩
    | cons v l =>
      cases l with
      | nil => intro h2 h3; exact ⟨by simp [holds_or, h1, h2], by simp [h3]⟩
      | cons w l =>
        intro h2 _
        show (Term.or rc.2 (twoIn items)).holds M = true
        simp [holds_or, h2]


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
