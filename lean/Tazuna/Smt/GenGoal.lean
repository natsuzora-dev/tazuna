import Tazuna.Smt.UnrollCover
import Tazuna.Semantics.GenTarget

/-! generate's goal on an unrolled run: the last step answers in a class the target aims at (`genGoal`). The answer's
class is read off the step's terms: a command's admission, `decide` and `ensures`, a query's admission, and the names
of the rules a request breaks. A rule's name term is compared as SMT-LIB strings compare (`nameIsT`), which holds of
every value exactly when its string is the name, so the goal misses no run. With `runs_covered` this gives T6b
(`generate_unreached`): a depth with no model has no run of that many valid inputs, within the slots and faulting
nowhere, whose last step answers in the target's class. Events and requests are classes too; their goals need the
events and requests a step's terms show, which the step's theorems do not relate yet. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The string `n` denotes is `r`: `str.++` with the empty string is `n` itself as a string. -/
def nameIsT (n : Term) (r : String) : Term := .eq (.cat n (.str "")) (.str r)

theorem holds_nameIsT {M : Model} (n : Term) (r : String) : Holds M (nameIsT n r) ↔ (n.denote M).toStr = r := by
  simp only [nameIsT, Holds, Term.denote, Val.toBool]
  cases Term.denote M n <;> simp [Val.toStr, BEq.beq, Val.beq]

/-- Some rule is broken whose name term meets `want`. -/
def brokenAnyT (rules : List (Term × Term)) (want : Term → Term) : Term :=
  anyT (rules.map fun r => andT (.not r.2) (want r.1))

/-- An Invalid answer naming the rule `r` (none: a rule whose name is none of the literals `lits`): admission's
`callers`, or a broken `accepts` rule. -/
def invalidT (lits : List String) (callerOk : Term) (rules : List (Term × Term)) : Option String → Term
  | some r => .or (andT (.not callerOk) (.bool (r == "callers"))) (andT callerOk (brokenAnyT rules (nameIsT · r)))
  | none => andT callerOk (brokenAnyT rules fun n => allT (lits.map fun l => .not (nameIsT n l)))

/-- The value `x` of the type `t` is built with the constructor named `V` (none for a type with no constructors). -/
def variantT (L : Layout) (T : List TypeDecl) (t : Ty) (V : Option String) (x : Term) : Term :=
  match t with
  | .adt 0 _ _ => anyT ((List.range 2).filterMap fun k =>
      if variantName T 0 k == V then some (.eq x (.bool (k == 0))) else none)
  | .adt (i + 1) a vs => match L.find? (.adt (i + 1) a vs) with
    | some (d, _) => anyT ((List.range vs.length).filterMap fun k =>
        if variantName T (i + 1) k == V then some (.is d k x) else none)
    | none => ff
  | _ => .bool (V == none)

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV} (rules : RuleNames) (g : GenTarget)

/-- Where a step of the kind answers in a class the target aims at, by the kind's terms: a command's or query's answer;
other kinds give no answer line. -/
def kindHitT {shs : List (PendingShape v.event)} {n : Nat} : SymInput v shs n → StepOut v → Term
  | .command i _ _, .command o =>
    let x := v.commands.get i
    let admitted := andT o.callerOk (allT (o.rules.map (·.2)))
    match g with
    | .accepted c => if c == x.name then andT admitted (andT o.decided.ok (allT (o.decided.ensures.map (·.2)))) else ff
    | .rejected c V =>
      if c == x.name then andT admitted (andT (.not o.decided.ok) (variantT L T x.rejection V o.decided.rejection))
      else ff
    | .invalid c r => if c == x.name then invalidT (rules.literals c) o.callerOk o.rules r else ff
    | _ => ff
  | .query i _ _, .query o =>
    let q := v.queries.get i
    match g with
    | .answered c => if c == q.name then andT o.callerOk (allT (o.rules.map (·.2))) else ff
    | .invalid c r => if c == q.name then invalidT (rules.literals c) o.callerOk o.rules r else ff
    | _ => ff
  | _, _ => ff

/-- generate's goal: the last step takes a kind whose step answers in a class the target aims at. -/
def genGoal {n : Nat} (sts : List (UnrollStep v n)) : Term :=
  match sts.getLast? with
  | some st => anyT (st.kinds.map fun k => andT (st.picks k) (kindHitT L T rules g k.1 k.2.out))
  | none => ff

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

theorem altIndex_rel {d : Nat} : (k0 : Nat) → (i : Nat) → (a : List Ty) → (vs : List (List Ty)) →
    (h : (Ty.adt i a vs).isData = true) → (x : (Ty.adt i a vs).den0) → {w : Val} →
    RelAlts L d k0 vs (Ty.up _ h x) w → ∃ vals, w = .ctor d (k0 + altIndex vs x) vals
  | _, _, _, [], _, x, _, _ => nomatch x
  | k0, i, a, fs :: vs, h, .inl x, w, hr => by
    have hfs : (Ty.tuple fs).isData = true := by
      simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at h ⊢; exact h.1
    rw [Ty.up_inl i a fs vs h hfs x] at hr
    obtain ⟨vals, rfl, -⟩ := hr
    exact ⟨vals, by simp [altIndex]⟩
  | k0, i, a, fs :: vs, h, .inr y, w, hr => by
    have hvs : (Ty.adt i a vs).isData = true := by
      simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at h ⊢; exact h.2
    rw [Ty.up_inr i a fs vs h hvs y] at hr
    obtain ⟨vals, hv⟩ := altIndex_rel (k0 + 1) i a vs hvs y hr
    exact ⟨vals, by rw [hv]; simp [altIndex]; omega⟩

theorem altsBool_up (a : List Ty) (h : (Ty.adt 0 a [[], []]).isData = true) (x : (Ty.adt 0 a [[], []]).den0) :
    altsBool (Ty.up _ h x) = (altIndex [[], []] x == 0) := by
  rcases x with x | x | x
  · rw [Ty.up_inl 0 a [] [[]] h rfl x]; rfl
  · rw [Ty.up_inr 0 a [] [[]] h rfl (.inl x), Ty.up_inl 0 a [] [] rfl rfl x]; rfl
  · exact nomatch x

/-- The variant term holds of the constructor a value is built with. -/
theorem variantT_holds (t : Ty) (h : t.isData = true) (y : t.den0) {x : Term} (hr : RelV L t (Ty.up _ h y) (x.denote M)) :
    Holds M (variantT L T t (variantOf T t y) x) := by
  match t, h, y, hr with
  | .adt 0 a vs, h, y, hr =>
    obtain ⟨rfl, hv⟩ := hr
    simp only [variantT, variantOf]
    refine (holds_anyT _).2 ⟨.eq x (.bool (altIndex [[], []] y == 0)),
      List.mem_filterMap.2 ⟨altIndex [[], []] y, List.mem_range.2 (altIndex_lt _ y), by simp⟩, ?_⟩
    simp [Holds, Term.denote, hv, altsBool_up, Val.toBool, BEq.beq, Val.beq]
  | .adt (i + 1) a vs, h, y, hr =>
    obtain ⟨d, n, hf, hra⟩ := hr
    obtain ⟨vals, hv⟩ := altIndex_rel 0 (i + 1) a vs h y hra
    simp only [variantT, variantOf, hf]
    refine (holds_anyT _).2 ⟨.is d (altIndex vs y) x,
      List.mem_filterMap.2 ⟨altIndex vs y, List.mem_range.2 (altIndex_lt _ y), by simp⟩, ?_⟩
    simp [Holds, Term.denote, hv, Val.toBool]
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ | .id, _, _, _ | .list _, _, _, _ | .tuple _, _, _, _
  | .fn _ _, _, _, _ | .param _, _, _, _ | .bag _, _, _, _ | .table _ _, _, _, _ | .dsl _ _, _, _, _ =>
    simp [variantT, variantOf, Holds, Term.denote, Val.toBool]

theorem invalidT_holds {lits : List String} {callerOk : Term} {rules : List (Term × Term)} {ns : List String}
    (hns : ns = if (callerOk.denote M).toBool then brokenIn M rules else ["callers"]) {r : Option String} {r' : String}
    (hr : r' ∈ ns) (hcov : (match r with | some r => r == r' | none => !lits.contains r') = true)
    (hlit : "callers" ∈ lits) : Holds M (invalidT lits callerOk rules r) := by
  by_cases hc : Holds M callerOk
  · simp only [show (callerOk.denote M).toBool = true from hc, ite_true] at hns
    subst hns
    obtain ⟨p, hp, hnb, hname⟩ := mem_brokenIn hr
    cases r with
    | some r =>
      simp only [beq_iff_eq] at hcov
      subst hcov
      refine (holds_or _ _).2 (.inr ((holds_andT _ _).2 ⟨hc, (holds_anyT _).2 ⟨_, List.mem_map_of_mem hp, ?_⟩⟩))
      exact (holds_andT _ _).2 ⟨(holds_not _).2 hnb, (holds_nameIsT _ _).2 hname⟩
    | none =>
      refine (holds_andT _ _).2 ⟨hc, (holds_anyT _).2 ⟨_, List.mem_map_of_mem hp, ?_⟩⟩
      refine (holds_andT _ _).2 ⟨(holds_not _).2 hnb, (holds_allT _).2 fun t ht => ?_⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ht
      refine (holds_not _).2 fun hn => ?_
      rw [holds_nameIsT, hname] at hn
      subst hn
      simp [hl] at hcov
  · simp only [show (callerOk.denote M).toBool = false by simpa [Holds] using hc, Bool.false_eq_true, ite_false]
      at hns
    subst hns
    simp only [List.mem_singleton] at hr
    subst hr
    cases r with
    | some r =>
      simp only [beq_iff_eq] at hcov
      subst hcov
      exact (holds_or _ _).2 (.inl ((holds_andT _ _).2 ⟨(holds_not _).2 hc, by simp [Holds, Term.denote, Val.toBool]⟩))
    | none => simp [hlit] at hcov

/-- Whether the step's answer is in a class the target aims at. -/
def Hits (T : List TypeDecl) (v : ServiceV) (rules : RuleNames) (g : GenTarget) (x : Input v) (r : Result v) : Prop :=
  ∃ c ∈ answerClasses T v x r.outcome, g.covers rules c = true

theorem covers_invalid {rules : RuleNames} {g : GenTarget} {q r' : String}
    (h : g.covers rules (.invalid q r') = true) :
    ∃ rr, g = .invalid q rr ∧ (match rr with | some r => r == r' | none => !(rules.literals q).contains r') = true := by
  cases g with
  | invalid c rr =>
    cases rr <;> simp only [GenTarget.covers, Bool.and_eq_true, beq_iff_eq] at h
    · obtain ⟨rfl, h2⟩ := h; exact ⟨none, rfl, h2⟩
    · obtain ⟨rfl, h2⟩ := h; exact ⟨some _, rfl, by simpa using h2⟩
  | _ => simp [GenTarget.covers] at h

theorem finished_outcome {shs : List (PendingShape v.event)} {fo : FinishOut v} {s0 : State v} {a : Step.Acc v}
    {outcome : Outcome} {r : Result v} (hf : Finished M L T shs fo s0 a outcome r) (hno : ∀ f, r.outcome ≠ .fault f) :
    r.outcome = outcome := by
  obtain ⟨-, hm⟩ := hf
  split at hm
  · subst hm; exact absurd rfl (hno _)
  · split at hm
    · subst hm; exact absurd rfl (hno _)
    · obtain ⟨_, _, _, _, _, rfl, -⟩ := hm; rfl

/-- Where a kind's terms say what the step's result is and the step does not fault, the kind's hit term holds when the
answer is in a class the target aims at. -/
theorem kindHitT_holds {rules : RuleNames} {g : GenTarget} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v (shapes v) n} {out : StepOut v} {s : State v} {x : Input v}
    (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) (hhit : Hits T v rules g x (step T v s x)) :
    Holds M (kindHitT L T rules g inp out) := by
  obtain ⟨c, hcm, hcov⟩ := hhit
  have hlit : ∀ name, "callers" ∈ rules.literals name := fun _ => List.mem_cons_self ..
  generalize step T v s x = r at hrel hno hcm
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases out with
    | command o =>
      simp only [StepOut.Rel] at hrel
      simp only [kindHitT]
      split at hrel
      · rename_i hcall
        have hcall' : Holds M o.callerOk := hcall
        split at hrel
        · rename_i m ms hr
          subst hrel
          simp only [answerClasses, List.mem_map] at hcm
          obtain ⟨r', hr', rfl⟩ := hcm
          obtain ⟨rr, rfl, hrr⟩ := covers_invalid hcov
          simp only [beq_self_eq_true, ite_true]
          exact invalidT_holds (by simp only [hcall, ite_true, hr]) hr' hrr (hlit _)
        · rename_i hr
          have hrules : Holds M (allT (o.rules.map (·.2))) := (holds_allT_rules _).2 hr
          split at hrel
          · rename_i hok
            split at hrel
            · subst hrel; exact absurd rfl (hno _)
            · rename_i he
              rw [finished_outcome hrel hno] at hcm
              simp only [answerClasses, List.mem_singleton] at hcm
              subst hcm
              cases g <;> simp only [GenTarget.covers, beq_iff_eq, Bool.false_eq_true] at hcov
              subst hcov
              simp only [beq_self_eq_true, ite_true, holds_andT]
              exact ⟨⟨hcall', hrules⟩, hok, (holds_allT_rules _).2 he⟩
          · rename_i hok
            obtain ⟨-, j, hj, hjr⟩ := hrel
            rw [hj] at hcm
            simp only [answerClasses, List.mem_singleton] at hcm
            subst hcm
            cases g <;> simp only [GenTarget.covers, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hcov
            obtain ⟨rfl, rfl⟩ := hcov
            simp only [beq_self_eq_true, ite_true, holds_andT, holds_not]
            exact ⟨⟨hcall', hrules⟩, hok, variantT_holds _ _ j hjr⟩
      · rename_i hcall
        have hcall' : ¬ Holds M o.callerOk := hcall
        subst hrel
        simp only [answerClasses, List.mem_map, List.mem_singleton, exists_eq_left] at hcm
        subst hcm
        obtain ⟨rr, rfl, hrr⟩ := covers_invalid hcov
        simp only [beq_self_eq_true, ite_true]
        have hf : (o.callerOk.denote M).toBool = false := by simpa using hcall
        exact invalidT_holds (by simp only [hf, Bool.false_eq_true, ite_false]) (List.mem_singleton_self _) hrr (hlit _)
    | _ => simp only [StepOut.Rel] at hrel
  | query i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
    cases out with
    | query o =>
      obtain ⟨-, hq⟩ := hrel
      simp only [kindHitT]
      have hinv : ∀ ns, o.invalid M = some ns → ns = if (o.callerOk.denote M).toBool then brokenIn M o.rules else ["callers"] :=
        fun ns h => by
          simp only [QueryOut.invalid] at h
          split at h
          · rename_i hcall
            have hcall' : Holds M o.callerOk := hcall
            split at h
            · cases h
            · rename_i m ms hb; cases h; simp only [hcall, ite_true, hb]
          · rename_i hcall
            have hf : (o.callerOk.denote M).toBool = false := by simpa using hcall
            cases h; simp only [hf, Bool.false_eq_true, ite_false]
      cases hro : r.outcome with
      | invalid ns =>
        rw [hro] at hq hcm
        simp only [answerClasses, List.mem_map] at hcm
        obtain ⟨r', hr', rfl⟩ := hcm
        obtain ⟨rr, rfl, hrr⟩ := covers_invalid hcov
        simp only [beq_self_eq_true, ite_true]
        exact invalidT_holds (hinv ns hq) hr' hrr (hlit _)
      | answered w =>
        rw [hro] at hq hcm
        obtain ⟨t, y⟩ := w
        obtain ⟨hnone, -⟩ := hq
        simp only [answerClasses, List.mem_singleton] at hcm
        subst hcm
        cases g <;> simp only [GenTarget.covers, beq_iff_eq, Bool.false_eq_true] at hcov
        subst hcov
        simp only [beq_self_eq_true, ite_true, holds_andT]
        simp only [QueryOut.invalid] at hnone
        split at hnone
        · rename_i hcall
          split at hnone
          · rename_i hb; exact ⟨hcall, (holds_allT_rules _).2 hb⟩
          · cases hnone
        · cases hnone
      | _ => rw [hro] at hq; exact hq.elim
    | _ => simp only [StepOut.Rel] at hrel
  | answer k j to w =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    simp [answerClasses] at hcm
  | unmatched t to w =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    simp [answerClasses] at hcm
  | event i w =>
    obtain ⟨value, rfl, -⟩ := decode_event hx
    simp [answerClasses] at hcm
  | clock w =>
    obtain ⟨time, rfl, -⟩ := decode_clock hx
    simp [answerClasses] at hcm

end

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

/-- The last step of a model's unrolled run on `ys ++ [x]` is the step on `x` from where `ys` leaves the run. -/
theorem unrollRun_last {M : Model} {hc : v.caller.isData = true} {n : Nat} (x : Input v) :
    (ys : List (Input v)) → (s : State v) → (sts : List (UnrollStep v n)) →
    UnrollRun L T M hc s sts (ys ++ [x]) → ∃ st, sts.getLast? = some st ∧ StepAt L T M hc st (run T v s ys).1 x
  | [], _, [st], ⟨_, hat, _⟩ => ⟨st, rfl, hat⟩
  | [], _, _ :: _ :: _, ⟨_, _, h⟩ => h.elim
  | [], _, [], h => h.elim
  | _ :: _, _, [], h => h.elim
  | y :: ys, s, st :: sts, ⟨_, _, h⟩ => by
    obtain ⟨st', hl, hat⟩ := unrollRun_last x ys _ sts h
    refine ⟨st', ?_, by simpa [run] using hat⟩
    cases sts with
    | nil => cases ys <;> exact h.elim
    | cons a l => simpa [List.getLast?_cons_cons] using hl

/-- T6b: where generate's script for the target at depth `d` has no input kind refused and no model, no run from the
initial state of `d` inputs that fit the slots and are valid, whose steps stay within the slots and fault nowhere,
answers at its last step in a class the target aims at. generate's "unreached within k steps" is this at every depth up
to k, so no such run of at most k inputs answers in that class at any step. -/
theorem generate_unreached (chk : Checked P E T v) (senv : StepEnv L (shapes v)) (hL : SortedLayout L)
    {rules : RuleNames} {g : GenTarget} {d : Nat} {U : Unrolled v senv.nT}
    (hu : unroll L T P v senv d (genGoal L T rules g) = .ok U) (hnr : U.refused = []) (hun : Unsat L U.ask)
    {ys : List (Input v)} {x : Input v} (hlen : ys.length + 1 = d)
    (hfits : RunFits L T P v chk.callerData (Step.State.init v) (ys ++ [x])) :
    ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) ys).1 x) := by
  intro hhit
  obtain ⟨M, hM, hrun, hiff⟩ := runs_covered chk senv hL hu hnr (by simp [hlen]) hfits
  obtain ⟨a, ha, hna⟩ := hun.noModel M hM
  refine hna (hiff.2 ?_ a ha)
  obtain ⟨st, hlast, ⟨k, hk, hpk, hdec, hrel⟩, hno, -⟩ := unrollRun_last x ys _ _ hrun
  simp only [genGoal, hlast]
  exact (holds_anyT _).2 ⟨_, List.mem_map_of_mem hk, (holds_andT _ _).2 ⟨hpk, kindHitT_holds hdec hrel hno hhit⟩⟩

end

end Tazuna.Smt
