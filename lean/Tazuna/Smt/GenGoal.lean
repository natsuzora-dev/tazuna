import Tazuna.Smt.UnrollCover
import Tazuna.Semantics.GenTarget

/-! generate's goal on an unrolled run: the last step shows a class of out line the target aims at (`genGoal`). An
answer's class is read off the step's terms: a command's admission, `decide` and `ensures`, a query's admission, and
the names of the rules a request breaks. A rule's name term is compared as SMT-LIB strings compare (`nameIsT`), which
holds of every value exactly when its string is the name, so the goal misses no run. An event's class is read off the
event slots of the step's end (`Finished` relates them to the events applied), where the step reaches its end. With
`runs_covered` this gives T6b (`generate_unreached`): a depth with no model has no run of that many valid inputs,
within the slots and faulting nowhere, whose last step shows the target's class. The goal reads the kind the step
takes, the one decoding reads, so it holds only of runs that show that class (`generate_sound`). -/

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
variable {v : ServiceV} {n : Nat}

/-- `h` of the kind the step takes (`UnrollStep.taken`): of the first kind it picks; false where it picks none. -/
def UnrollStep.takenT (st : UnrollStep v n) (h : SymInput v (shapes v) n × EncodedStep v → Term) : Term :=
  st.kinds.foldr (fun k r => .ite (st.picks k) (h k) r) ff

theorem holds_takenT {M : Model} (st : UnrollStep v n) (h : SymInput v (shapes v) n × EncodedStep v → Term) :
    Holds M (st.takenT h) ↔ ∃ k, st.taken M = some k ∧ Holds M (h k) := by
  simp only [UnrollStep.takenT, UnrollStep.taken]
  induction st.kinds with
  | nil => simp [ff, Holds, Term.denote, Val.toBool]
  | cons k ks ih =>
    simp only [List.foldr_cons, List.find?_cons, holds_ite]
    cases (st.picks k).denote M |>.toBool <;> simp [ih]

end

/-- Some occupied event slot holds an event built with the constructor `V`. -/
def eventsHitT (L : Layout) (T : List TypeDecl) (v : ServiceV) (S : List (Slot 1)) (V : Option String) : Term :=
  anyT (S.map fun sl => andT sl.1 (variantT L T v.event V sl.2[0]))

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV} (rules : RuleNames) (g : GenTarget)

/-- Where a step of the kind answers in a class the target aims at, by the kind's terms: a command's or query's answer;
other kinds give no answer line. -/
def answerHitT {shs : List (PendingShape v.event)} {n : Nat} : SymInput v shs n → StepOut v → Term
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

/-- Where a step of the kind reaches its end, `hit` of the end's terms; nowhere for a kind with no end. -/
def endHitT (out : StepOut v) (hit : FinishOut v → Term) : Term :=
  match out.finish? with
  | some fo => andT out.reached (hit fo)
  | none => ff

/-- Where a step of the kind shows a class of out line the target aims at, by the kind's terms: for an event, some
event the step applies is built with the target's constructor; otherwise the step's answer. -/
def kindHitT {n : Nat} (inp : SymInput v (shapes v) n) (out : StepOut v) : Term :=
  match g with
  | .event V => endHitT out fun fo => eventsHitT L T v fo.events V
  | _ => answerHitT L T rules g inp out

/-- generate's goal: the kind the last step takes answers in a class the target aims at. -/
def genGoal {n : Nat} (sts : List (UnrollStep v n)) : Term :=
  match sts.getLast? with
  | some st => st.takenT fun k => kindHitT L T rules g k.1 k.2.out
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

theorem brokenIn_mem {rules : List (Term × Term)} {rule : Term × Term} (hm : rule ∈ rules) (hb : ¬ Holds M rule.2) :
    (rule.1.denote M).toStr ∈ brokenIn M rules :=
  List.mem_filterMap.2 ⟨rule, hm, by simp only [Holds] at hb; simp [hb]⟩

/-- The variant term holds only of the constructor a value is built with. -/
theorem variantT_sound (t : Ty) (h : t.isData = true) (y : t.den0) {x : Term} {V : Option String}
    (hr : RelV L t (Ty.up _ h y) (x.denote M)) (hv : Holds M (variantT L T t V x)) : variantOf T t y = V := by
  match t, h, y, hr with
  | .adt 0 a vs, h, y, hr =>
    obtain ⟨rfl, hx⟩ := hr
    simp only [variantT, variantOf] at hv ⊢
    obtain ⟨_, hm, ht⟩ := (holds_anyT _).1 hv
    obtain ⟨k, hk, hkt⟩ := List.mem_filterMap.1 hm
    split at hkt
    · rename_i hV
      cases hkt
      simp only [Holds, Term.denote, hx, altsBool_up, Val.toBool, BEq.beq, Val.beq] at ht
      have hk2 := List.mem_range.1 hk
      have hy2 := altIndex_lt [[], []] y
      have : k = altIndex [[], []] y := by
        simp only [List.length_cons, List.length_nil] at hy2
        revert ht; generalize altIndex [[], []] y = m at hy2 ⊢
        rcases k with _ | _ | k <;> rcases m with _ | _ | m <;> simp <;> omega
      subst this
      simpa using hV
    · cases hkt
  | .adt (i + 1) a vs, h, y, hr =>
    obtain ⟨d, n, hf, hra⟩ := hr
    obtain ⟨vals, hval⟩ := altIndex_rel 0 (i + 1) a vs h y hra
    simp only [variantT, variantOf, hf] at hv ⊢
    obtain ⟨_, hm, ht⟩ := (holds_anyT _).1 hv
    obtain ⟨k, -, hkt⟩ := List.mem_filterMap.1 hm
    split at hkt
    · rename_i hV
      cases hkt
      simp only [Holds, Term.denote, hval, Val.toBool, beq_self_eq_true, Bool.true_and, beq_iff_eq, Nat.zero_add] at ht
      subst ht
      simpa using hV
    · cases hkt
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ | .id, _, _, _ | .list _, _, _, _ | .tuple _, _, _, _
  | .fn _ _, _, _, _ | .param _, _, _, _ | .bag _, _, _, _ | .table _ _, _, _, _ | .dsl _ _, _, _, _ =>
    simp only [variantT, variantOf, Holds, Term.denote, Val.toBool, beq_iff_eq] at hv ⊢
    exact hv.symm

/-- The invalid term holds only where the step names a rule the target aims at: admission's `callers`, else a broken
rule. -/
theorem invalidT_sound {lits : List String} {callerOk : Term} {rules : List (Term × Term)} {r : Option String}
    (h : Holds M (invalidT lits callerOk rules r)) :
    ∃ r' ∈ (if (callerOk.denote M).toBool then brokenIn M rules else ["callers"]),
      (match r with | some r => r == r' | none => !lits.contains r') = true := by
  have hrule : ∀ {want : Term → Term}, Holds M callerOk → Holds M (brokenAnyT rules want) →
      ∃ rule ∈ rules, (rule.1.denote M).toStr ∈ brokenIn M rules ∧ Holds M (want rule.1) := fun hc hb => by
    obtain ⟨_, hm1, ht⟩ := (holds_anyT _).1 hb
    obtain ⟨rule, hm2, rfl⟩ := List.mem_map.1 hm1
    obtain ⟨hnb, hw⟩ := (holds_andT _ _).1 ht
    exact ⟨rule, hm2, brokenIn_mem hm2 ((holds_not _).1 hnb), hw⟩
  cases r with
  | some r =>
    rcases (holds_or _ _).1 h with h | h
    · obtain ⟨hnc, hr⟩ := (holds_andT _ _).1 h
      have hf : (callerOk.denote M).toBool = false := by simpa [Holds] using (holds_not _).1 hnc
      simp only [Holds, Term.denote, Val.toBool] at hr
      exact ⟨"callers", by simp [hf], hr⟩
    · obtain ⟨hc, hb⟩ := (holds_andT _ _).1 h
      obtain ⟨rule, -, hm, hn⟩ := hrule hc hb
      refine ⟨_, by simpa [show (callerOk.denote M).toBool = true from hc] using hm, ?_⟩
      simp [(holds_nameIsT _ _).1 hn]
  | none =>
    obtain ⟨hc, hb⟩ := (holds_andT _ _).1 h
    obtain ⟨rule, -, hm, hn⟩ := hrule hc hb
    refine ⟨_, by simpa [show (callerOk.denote M).toBool = true from hc] using hm, ?_⟩
    simp only [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
    intro l hl heq
    have := (holds_allT _).1 hn _ (List.mem_map_of_mem hl)
    exact (holds_not _).1 this ((holds_nameIsT _ _).2 heq)

/-- Whether the step's answer is in a class the target aims at. -/
def AnswerHits (T : List TypeDecl) (v : ServiceV) (rules : RuleNames) (g : GenTarget) (x : Input v) (r : Result v) : Prop :=
  ∃ c ∈ answerClasses T v x r.outcome, g.covers rules c = true

/-- Whether the step shows a class of out line the target aims at: its answer, an event it applies, a request it
sends. -/
def Hits (T : List TypeDecl) (v : ServiceV) (rules : RuleNames) (g : GenTarget) (x : Input v) (r : Result v) : Prop :=
  ∃ c ∈ classes T v x r, g.covers rules c = true

theorem hits_answer {rules : RuleNames} {g : GenTarget} (hev : ∀ V, g ≠ .event V) (hrq : ∀ e n, g ≠ .request e n)
    {x : Input v} {r : Result v} : Hits T v rules g x r ↔ AnswerHits T v rules g x r := by
  simp only [Hits, AnswerHits, classes, List.mem_append, List.mem_map]
  refine ⟨fun ⟨c, hc, hcov⟩ => ?_, fun ⟨c, hc, hcov⟩ => ⟨c, .inl (.inl hc), hcov⟩⟩
  rcases hc with (hc | ⟨ev, -, rfl⟩) | ⟨o, -, rfl⟩
  · exact ⟨c, hc, hcov⟩
  · cases g <;> simp [GenTarget.covers] at hcov
    exact absurd rfl (hev _)
  · cases g <;> simp [GenTarget.covers] at hcov
    exact absurd rfl (hrq _ _)

theorem hits_event {rules : RuleNames} {V : Option String} {x : Input v} {r : Result v} :
    Hits T v rules (.event V) x r ↔ ∃ ev ∈ r.events, variantOf T v.event ev = V := by
  simp only [Hits, classes, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨c, (hc | ⟨ev, hev, rfl⟩) | ⟨o, -, rfl⟩, hcov⟩
    · cases x <;> cases hr : r.outcome <;> simp [answerClasses, hr] at hc <;>
        first | (subst hc; simp [GenTarget.covers] at hcov) | (obtain ⟨_, -, rfl⟩ := hc; simp [GenTarget.covers] at hcov)
    · exact ⟨ev, hev, (by simpa [GenTarget.covers] using hcov : V = _).symm⟩
    · simp [GenTarget.covers] at hcov
  · rintro ⟨ev, hev, rfl⟩
    exact ⟨_, .inl (.inr ⟨ev, hev, rfl⟩), by simp [GenTarget.covers]⟩

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
theorem answerHitT_holds {rules : RuleNames} {g : GenTarget} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v (shapes v) n} {out : StepOut v} {s : State v} {x : Input v}
    (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) (hhit : AnswerHits T v rules g x (step T v s x)) :
    Holds M (answerHitT L T rules g inp out) := by
  obtain ⟨c, hcm, hcov⟩ := hhit
  have hlit : ∀ name, "callers" ∈ rules.literals name := fun _ => List.mem_cons_self ..
  generalize step T v s x = r at hrel hno hcm
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases out with
    | command o =>
      simp only [StepOut.Rel] at hrel
      simp only [answerHitT]
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
      simp only [answerHitT]
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

/-- The converse of `answerHitT_holds`: where a kind's terms say what the step's result is and the step does not fault,
the kind's hit term holds only when the answer is in a class the target aims at. -/
theorem answerHitT_sound {rules : RuleNames} {g : GenTarget} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v (shapes v) n} {out : StepOut v} {s : State v} {x : Input v}
    (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) (hh : Holds M (answerHitT L T rules g inp out)) :
    AnswerHits T v rules g x (step T v s x) := by
  generalize step T v s x = r at hrel hno
  have hff : ¬ Holds M ff := by simp [ff, Holds, Term.denote, Val.toBool]
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases out with
    | command o =>
      simp only [StepOut.Rel] at hrel
      have hinv : ∀ {c rr}, g = .invalid c rr → c = (v.commands.get i).name →
          Holds M (invalidT (rules.literals c) o.callerOk o.rules rr) → AnswerHits T v rules g (.command i caller input) r :=
        fun {c rr} hg hcn hi => by
          subst hg hcn
          obtain ⟨r', hr', hcov⟩ := invalidT_sound hi
          refine ⟨.invalid (v.commands.get i).name r', ?_, by cases rr <;> simpa [GenTarget.covers] using hcov⟩
          split at hrel
          · rename_i hcall
            simp only [hcall, ite_true] at hr'
            split at hrel
            · rename_i m ms hb; subst hrel; rw [hb] at hr'; simpa [answerClasses] using hr'
            · rename_i hb; rw [hb] at hr'; cases hr'
          · rename_i hcall
            simp only [hcall, Bool.false_eq_true, ite_false] at hr'
            subst hrel; simpa [answerClasses] using hr'
      cases g with
      | invalid c rr =>
        simp only [answerHitT] at hh
        split at hh
        · rename_i hcn
          exact hinv rfl (by simpa using hcn) hh
        · exact absurd hh hff
      | accepted c =>
        simp only [answerHitT] at hh
        split at hh
        · rename_i hcn
          obtain ⟨⟨hcall, hrules⟩, hok, hens⟩ := by simpa only [holds_andT] using hh
          simp only [show (o.callerOk.denote M).toBool = true from hcall, ite_true,
            (holds_allT_rules _).1 hrules, show (o.decided.ok.denote M).toBool = true from hok,
            (holds_allT_rules _).1 hens] at hrel
          refine ⟨.accepted (v.commands.get i).name, ?_, by simpa [GenTarget.covers] using hcn⟩
          rw [finished_outcome hrel hno]
          simp [answerClasses]
        · exact absurd hh hff
      | rejected c V =>
        simp only [answerHitT] at hh
        split at hh
        · rename_i hcn
          obtain ⟨⟨hcall, hrules⟩, hok, hv⟩ := by simpa only [holds_andT, holds_not] using hh
          have hok' : (o.decided.ok.denote M).toBool = false := by simpa [Holds] using hok
          simp only [show (o.callerOk.denote M).toBool = true from hcall, ite_true,
            (holds_allT_rules _).1 hrules, hok', Bool.false_eq_true, ite_false] at hrel
          obtain ⟨-, j, hj, hjr⟩ := hrel
          refine ⟨.rejected (v.commands.get i).name (variantOf T _ j), by simp [hj, answerClasses], ?_⟩
          simp only [GenTarget.covers, Bool.and_eq_true, beq_iff_eq]
          exact ⟨by simpa using hcn, (variantT_sound _ _ j hjr hv).symm⟩
        · exact absurd hh hff
      | _ => exact absurd hh hff
    | _ => simp only [StepOut.Rel] at hrel
  | query i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
    cases out with
    | query o =>
      obtain ⟨-, hq⟩ := hrel
      cases g with
      | answered c =>
        simp only [answerHitT] at hh
        split at hh
        · rename_i hcn
          obtain ⟨hcall, hrules⟩ := (holds_andT _ _).1 hh
          have hnone : o.invalid M = none := by
            simp only [QueryOut.invalid, show (o.callerOk.denote M).toBool = true from hcall, ite_true,
              (holds_allT_rules _).1 hrules]
          cases hro : r.outcome with
          | answered w =>
            exact ⟨.answered (v.queries.get i).name, by simp [answerClasses, hro],
              by simpa [GenTarget.covers] using hcn⟩
          | invalid ns => rw [hro] at hq; simp only [QueryOut.Rel] at hq; rw [hnone] at hq; cases hq
          | _ => rw [hro] at hq; exact hq.elim
        · exact absurd hh hff
      | invalid c rr =>
        simp only [answerHitT] at hh
        split at hh
        · rename_i hcn
          obtain ⟨r', hr', hcov⟩ := invalidT_sound hh
          have hsome : o.invalid M = some (if (o.callerOk.denote M).toBool then brokenIn M o.rules else ["callers"]) := by
            simp only [QueryOut.invalid]
            split
            · rename_i hcall
              simp only [hcall, ite_true] at hr' ⊢
              split
              · rename_i hb; rw [hb] at hr'; cases hr'
              · rename_i m ms hb; rw [hb]
            · rename_i hcall; simp
          cases hro : r.outcome with
          | invalid ns =>
            rw [hro] at hq
            simp only [QueryOut.Rel, hsome, Option.some.injEq] at hq
            subst hq
            refine ⟨.invalid (v.queries.get i).name r', ?_,
              by cases rr <;> simpa [GenTarget.covers, beq_iff_eq.1 hcn] using hcov⟩
            simp only [answerClasses, hro, List.mem_map]
            exact ⟨r', hr', rfl⟩
          | answered w =>
            obtain ⟨t, y⟩ := w
            rw [hro] at hq; obtain ⟨hq, -⟩ := hq; rw [hsome] at hq; cases hq
          | _ => rw [hro] at hq; exact hq.elim
        · exact absurd hh hff
      | _ => exact absurd hh hff
    | _ => simp only [StepOut.Rel] at hrel
  | answer k j to w => cases out <;> exact absurd hh hff
  | unmatched t to w => cases out <;> exact absurd hh hff
  | event i w => cases out <;> exact absurd hh hff
  | clock w => cases out <;> exact absurd hh hff

/-- Some occupied slot meets `Q`: then some item the slots hold is one whose slot's items meet it. -/
theorem anySlots_sound {w : Nat} {α : Type} {E : α → List Val → Prop} (Q : SlotItems w → Term) :
    {S : List (Slot w)} → {sv : List (Bool × List Val)} → {ys : List α} → SlotsDen M S sv → Holds2 E ys sv →
    Holds M (anyT (S.map fun sl => andT sl.1 (Q sl.2))) → ∃ y ∈ ys, ∃ xs : SlotItems w, E y (Term.denotes M xs.1) ∧
      Holds M (Q xs)
  | [], [], _, _, _, h => by simp [holds_anyT] at h
  | (f, xs) :: S, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, he, h => by
    simp only [List.map_cons, holds_anyT, List.mem_cons] at h
    obtain ⟨t, ht | ht, hh⟩ := h
    · subst ht
      obtain ⟨hfh, hq⟩ := (holds_andT _ _).1 hh
      have hb : b = true := by simpa [Holds, hf, Val.toBool] using hfh
      subst hb
      simp only [Holds2, occupied, ite_true, List.filterMap_cons] at he
      match ys, he with
      | y :: _, ⟨hy, _⟩ => exact ⟨y, List.mem_cons_self .., xs, by rw [hx]; exact hy, hq⟩
    · have hrest : Holds M (anyT (S.map fun sl => andT sl.1 (Q sl.2))) := (holds_anyT _).2 ⟨t, ht, hh⟩
      cases b
      · exact anySlots_sound Q hS (by simpa [Holds2, occupied] using he) hrest
      · simp only [Holds2, occupied, ite_true, List.filterMap_cons] at he
        match ys, he with
        | _ :: ys', ⟨_, he'⟩ =>
          obtain ⟨y, hy, r⟩ := anySlots_sound Q hS he' hrest
          exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

/-- An item the slots hold whose slot's items meet `Q` makes some occupied slot meet it. -/
theorem anySlots_holds {w : Nat} {α : Type} {E : α → List Val → Prop} (Q : SlotItems w → Term) {y : α}
    (hq : ∀ xs : SlotItems w, E y (Term.denotes M xs.1) → Holds M (Q xs)) :
    {S : List (Slot w)} → {sv : List (Bool × List Val)} → {ys : List α} → SlotsDen M S sv → Holds2 E ys sv →
    y ∈ ys → Holds M (anyT (S.map fun sl => andT sl.1 (Q sl.2)))
  | [], [], ys, _, he, hy => by
    simp only [Holds2, occupied, List.filterMap_nil] at he
    cases ys with
    | nil => cases hy
    | cons _ _ => exact he.elim
  | (f, xs) :: S, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, he, hy => by
    simp only [List.map_cons, holds_anyT, List.mem_cons]
    cases b
    · obtain ⟨t, ht, hh⟩ := (holds_anyT _).1 (anySlots_holds Q hq hS (by simpa [Holds2, occupied] using he) hy)
      exact ⟨t, .inr ht, hh⟩
    · simp only [Holds2, occupied, ite_true, List.filterMap_cons] at he
      match ys, he, hy with
      | y' :: ys', ⟨hy', he'⟩, hy =>
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨_, .inl rfl, (holds_andT _ _).2 ⟨by simp [Holds, hf, Val.toBool], hq xs (by rw [hx]; exact hy')⟩⟩
        · obtain ⟨t, ht, hh⟩ := (holds_anyT _).1 (anySlots_holds Q hq hS he' hy)
          exact ⟨t, .inr ht, hh⟩

theorem eventsHitT_sound {S : List (Slot 1)} {evs : List v.event.den0} (h : EventsRel M L S evs) {V : Option String}
    (hh : Holds M (eventsHitT L T v S V)) : ∃ ev ∈ evs, variantOf T v.event ev = V := by
  obtain ⟨sv, hS, h2⟩ := h
  unfold eventsHitT at hh
  obtain ⟨y, hy, xs, ⟨z, hz, hr⟩, hq⟩ := anySlots_sound (fun xs : SlotItems 1 => variantT L T v.event V xs[0]) hS h2 hh
  obtain ⟨ev, hev, rfl⟩ := List.mem_map.1 hy
  obtain ⟨a, rfl⟩ := SlotItems.one xs
  simp only [Term.denotes, List.cons.injEq, and_true] at hz
  subst hz
  exact ⟨ev, hev, variantT_sound _ _ ev hr hq⟩

theorem eventsHitT_holds {S : List (Slot 1)} {evs : List v.event.den0} (h : EventsRel M L S evs) {ev : v.event.den0}
    (hev : ev ∈ evs) : Holds M (eventsHitT L T v S (variantOf T v.event ev)) := by
  obtain ⟨sv, hS, h2⟩ := h
  unfold eventsHitT
  refine anySlots_holds (fun xs : SlotItems 1 => variantT L T v.event (variantOf T v.event ev) xs[0]) (fun xs ⟨z, hz, hr⟩ => ?_) hS h2 (List.mem_map_of_mem hev)
  obtain ⟨a, rfl⟩ := SlotItems.one xs
  simp only [Term.denotes, List.cons.injEq, and_true] at hz
  subst hz
  exact variantT_holds _ _ ev hr

theorem finish_quiet (s0 : State v) (a : Except Fault (Step.Acc v))
    (h : (Step.finish T s0 a .accepted).outcome ≠ .accepted) :
    (Step.finish T s0 a .accepted).events = [] ∧ (Step.finish T s0 a .accepted).out = [] := by
  unfold Step.finish at h ⊢
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · rename_i hs _ hi; simp [hs, hi] at h

/-- A step whose outcome is not `accepted` applies no event and sends no request. -/
theorem step_quiet (s : State v) (x : Input v) (h : (step T v s x).outcome ≠ .accepted) :
    (step T v s x).events = [] ∧ (step T v s x).out = [] := by
  cases x with
  | command i c y =>
    simp only [step] at h ⊢
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rename_i hx; rw [hx] at h; exact finish_quiet _ _ h
  | query i c y => simp only [step]; split <;> exact ⟨rfl, rfl⟩
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step] at h ⊢
    split
    · exact ⟨rfl, rfl⟩
    · rename_i p hp
      rw [hp] at h
      simp only at h ⊢
      split
      · exact ⟨rfl, rfl⟩
      · rename_i hq hs
        simp only [hs] at h ⊢
        split
        · exact ⟨rfl, rfl⟩
        · rename_i hb; simp only [hb] at h; exact finish_quiet _ _ h
  | event i value => exact finish_quiet _ _ h
  | clock time =>
    simp only [step] at h ⊢
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hlt
      simp only [hlt, ite_false] at h
      split
      · exact ⟨rfl, rfl⟩
      · rename_i hf; simp only [hf] at h; exact finish_quiet _ _ h

/-- Where a kind's terms say what the step's result is and the step does not fault: a step that reaches its end
ends as the end's terms say, from a step in progress with no event and no out line yet; and a step that applies an
event or sends a request reaches its end. -/
theorem rel_end {n : Nat} {hc : v.caller.isData = true} {inp : SymInput v (shapes v) n} {out : StepOut v}
    {s : State v} {x : Input v} (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) :
    (∀ fo, out.finish? = some fo → Holds M out.reached → ∃ s0 a, a.events = [] ∧ a.out = [] ∧
      Finished M L T (shapes v) fo s0 a .accepted (step T v s x)) ∧
    ((step T v s x).events ≠ [] ∨ (step T v s x).out ≠ [] →
      ∃ fo, out.finish? = some fo ∧ Holds M out.reached) := by
  refine ⟨fun fo hfo hre => ?_, fun hne => ?_⟩
  · generalize step T v s x = r at hrel hno
    cases inp with
    | command i sc si =>
      obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
      cases out with
      | command o =>
        simp only [StepOut.finish?, Option.some.injEq] at hfo
        subst hfo
        simp only [StepOut.reached, holds_andT] at hre
        obtain ⟨hcall, hr, hok, he⟩ := hre
        simp only [StepOut.Rel, show (o.callerOk.denote M).toBool = true from hcall, ite_true,
          (holds_allT_rules _).1 hr, show (o.decided.ok.denote M).toBool = true from hok,
          (holds_allT_rules _).1 he] at hrel
        exact ⟨_, _, rfl, rfl, hrel⟩
      | _ => simp only [StepOut.Rel] at hrel
    | query i sc si =>
      obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
      cases out <;> simp only [StepOut.Rel, StepOut.finish?] at hrel hfo
      all_goals cases hfo
    | answer k j to w =>
      obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
      cases out with
      | answer o =>
        simp only [StepOut.finish?, Option.some.injEq] at hfo
        subst hfo
        simp only [StepOut.reached] at hre
        simp only [StepOut.Rel, (holds_allT_rules _).1 hre] at hrel
        exact ⟨_, _, rfl, rfl, hrel⟩
      | unmatched _ => simp only [StepOut.finish?] at hfo; cases hfo
      | _ => simp only [StepOut.Rel] at hrel
    | unmatched t to w =>
      obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
      cases out with
      | answer o =>
        simp only [StepOut.finish?, Option.some.injEq] at hfo
        subst hfo
        simp only [StepOut.reached] at hre
        simp only [StepOut.Rel, (holds_allT_rules _).1 hre] at hrel
        exact ⟨_, _, rfl, rfl, hrel⟩
      | unmatched _ => simp only [StepOut.finish?] at hfo; cases hfo
      | _ => simp only [StepOut.Rel] at hrel
    | event i w =>
      obtain ⟨value, rfl, -⟩ := decode_event hx
      cases out with
      | event o =>
        simp only [StepOut.finish?, Option.some.injEq] at hfo
        subst hfo
        exact ⟨_, _, rfl, rfl, hrel⟩
      | _ => simp only [StepOut.Rel] at hrel
    | clock w =>
      obtain ⟨time, rfl, -⟩ := decode_clock hx
      cases out with
      | clock o =>
        simp only [StepOut.finish?, Option.some.injEq] at hfo
        subst hfo
        simp only [StepOut.reached, holds_andT, holds_not] at hre
        obtain ⟨hfw, hov⟩ := hre
        have hov' : (o.over.denote M).toBool = false := by simpa [Holds] using hov
        simp only [StepOut.Rel, show (o.forward.denote M).toBool = true from hfw, ite_true, hov',
          Bool.false_eq_true, ite_false] at hrel
        exact ⟨_, _, rfl, rfl, hrel⟩
      | _ => simp only [StepOut.Rel] at hrel
  · have hacc : (step T v s x).outcome = .accepted := by
      apply Classical.byContradiction; intro hna
      have := step_quiet s x hna
      rcases hne with h | h
      · exact h this.1
      · exact h this.2
    generalize step T v s x = r at hrel hno hacc
    cases inp with
    | command i sc si =>
      obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
      cases out with
      | command o =>
        simp only [StepOut.Rel] at hrel
        split at hrel
        · rename_i hcall
          split at hrel
          · subst hrel; cases hacc
          · rename_i hr
            split at hrel
            · rename_i hok
              split at hrel
              · subst hrel; cases hacc
              · rename_i he
                refine ⟨_, rfl, ?_⟩
                simp only [StepOut.reached, holds_andT]
                exact ⟨hcall, (holds_allT_rules _).2 hr, hok, (holds_allT_rules _).2 he⟩
            · obtain ⟨-, j, hj, -⟩ := hrel; rw [hj] at hacc; cases hacc
        · subst hrel; cases hacc
      | _ => simp only [StepOut.Rel] at hrel
    | query i sc si =>
      obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
      cases out with
      | query o => obtain ⟨-, hq⟩ := hrel; rw [hacc] at hq; exact hq.elim
      | _ => simp only [StepOut.Rel] at hrel
    | answer k j to w =>
      obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
      cases out with
      | answer o =>
        simp only [StepOut.Rel] at hrel
        split at hrel
        · subst hrel; cases hacc
        · rename_i hr; exact ⟨_, rfl, (holds_allT_rules _).2 hr⟩
      | unmatched _ => simp only [StepOut.Rel] at hrel; subst hrel; cases hacc
      | _ => simp only [StepOut.Rel] at hrel
    | unmatched t to w =>
      obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
      cases out with
      | answer o =>
        simp only [StepOut.Rel] at hrel
        split at hrel
        · subst hrel; cases hacc
        · rename_i hr; exact ⟨_, rfl, (holds_allT_rules _).2 hr⟩
      | unmatched _ => simp only [StepOut.Rel] at hrel; subst hrel; cases hacc
      | _ => simp only [StepOut.Rel] at hrel
    | event i w =>
      obtain ⟨value, rfl, -⟩ := decode_event hx
      cases out with
      | event o => exact ⟨_, rfl, holds_tt⟩
      | _ => simp only [StepOut.Rel] at hrel
    | clock w =>
      obtain ⟨time, rfl, -⟩ := decode_clock hx
      cases out with
      | clock o =>
        simp only [StepOut.Rel] at hrel
        split at hrel
        · rename_i hfw
          split at hrel
          · subst hrel; cases hacc
          · rename_i hov
            refine ⟨_, rfl, ?_⟩
            simp only [StepOut.reached, holds_andT, holds_not]
            exact ⟨hfw, by simpa [Holds] using hov⟩
        · subst hrel; cases hacc
      | _ => simp only [StepOut.Rel] at hrel

theorem finished_events {shs : List (PendingShape v.event)} {fo : FinishOut v} {s0 : State v} {a : Step.Acc v}
    {outcome : Outcome} {r : Result v} (hf : Finished M L T shs fo s0 a outcome r) (hno : ∀ f, r.outcome ≠ .fault f) :
    ∃ evs, r.events = a.events ++ evs ∧ EventsRel M L fo.events evs := by
  obtain ⟨-, hm⟩ := hf
  split at hm
  · subst hm; exact absurd rfl (hno _)
  · split at hm
    · subst hm; exact absurd rfl (hno _)
    · obtain ⟨_, _, _, evs, _, rfl, -, -, -, -, -, he⟩ := hm
      exact ⟨evs, rfl, he⟩

theorem hits_of_answer {rules : RuleNames} {g : GenTarget} {x : Input v} {r : Result v}
    (h : AnswerHits T v rules g x r) : Hits T v rules g x r := by
  obtain ⟨c, hc, hcov⟩ := h
  exact ⟨c, List.mem_append_left _ (List.mem_append_left _ hc), hcov⟩

/-- Where a kind's terms say what the step's result is and the step does not fault, the kind's hit term holds when
the step shows a class the target aims at. -/
theorem kindHitT_holds {rules : RuleNames} {g : GenTarget} (hrq : ∀ e n, g ≠ .request e n) {n : Nat}
    {hc : v.caller.isData = true} {inp : SymInput v (shapes v) n} {out : StepOut v} {s : State v} {x : Input v}
    (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) (hhit : Hits T v rules g x (step T v s x)) :
    Holds M (kindHitT L T rules g inp out) := by
  cases g with
  | event V =>
    obtain ⟨ev, hev, rfl⟩ := hits_event.1 hhit
    obtain ⟨fo, hfo, hre⟩ := (rel_end hx hrel hno).2 (.inl (List.ne_nil_of_mem hev))
    obtain ⟨s0, a, hae, -, hf⟩ := (rel_end hx hrel hno).1 fo hfo hre
    obtain ⟨evs, hevs, hE⟩ := finished_events hf hno
    rw [hevs, hae, List.nil_append] at hev
    simp only [kindHitT, endHitT, hfo]
    exact (holds_andT _ _).2 ⟨hre, eventsHitT_holds hE hev⟩
  | request e n => exact absurd rfl (hrq e n)
  | accepted _ | rejected _ _ | invalid _ _ | answered _ =>
    exact answerHitT_holds hx hrel hno ((hits_answer (fun _ h => by cases h) (fun _ _ h => by cases h)).1 hhit)

/-- The converse of `kindHitT_holds`: where a kind's terms say what the step's result is and the step does not fault,
the kind's hit term holds only when the step shows a class the target aims at. -/
theorem kindHitT_sound {rules : RuleNames} {g : GenTarget} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v (shapes v) n} {out : StepOut v} {s : State v} {x : Input v}
    (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) (hh : Holds M (kindHitT L T rules g inp out)) :
    Hits T v rules g x (step T v s x) := by
  cases g with
  | event V =>
    simp only [kindHitT, endHitT] at hh
    split at hh
    · rename_i fo hfo
      obtain ⟨hre, hev⟩ := (holds_andT _ _).1 hh
      obtain ⟨s0, a, hae, -, hf⟩ := (rel_end hx hrel hno).1 fo hfo hre
      obtain ⟨evs, hevs, hE⟩ := finished_events hf hno
      obtain ⟨ev, hm, rfl⟩ := eventsHitT_sound hE hev
      exact hits_event.2 ⟨ev, by rw [hevs, hae, List.nil_append]; exact hm, rfl⟩
    · simp [ff, Holds, Term.denote, Val.toBool] at hh
  | request e n => exact hits_of_answer (answerHitT_sound hx hrel hno hh)
  | accepted _ | rejected _ _ | invalid _ _ | answered _ => exact hits_of_answer (answerHitT_sound hx hrel hno hh)

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
    {rules : RuleNames} {g : GenTarget} (hrq : ∀ e n, g ≠ .request e n) {d : Nat} {U : Unrolled v senv.nT}
    (hu : unroll L T P v senv d (genGoal L T rules g) = .ok U) (hnr : U.refused = []) (hun : Unsat L U.ask)
    {ys : List (Input v)} {x : Input v} (hlen : ys.length + 1 = d)
    (hfits : RunFits L T P v chk.callerData (Step.State.init v) (ys ++ [x])) :
    ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) ys).1 x) := by
  intro hhit
  obtain ⟨M, hM, hrun, hiff⟩ := runs_covered chk senv hL hu hnr (by simp [hlen]) hfits
  obtain ⟨a, ha, hna⟩ := hun.noModel M hM
  refine hna (hiff.2 ?_ a ha)
  obtain ⟨st, hlast, ⟨k, hk, hdec, hrel⟩, hno, -⟩ := unrollRun_last x ys _ _ hrun
  simp only [genGoal, hlast]
  exact (holds_takenT _ _).2 ⟨k, hk, kindHitT_holds hrq hdec hrel hno hhit⟩

theorem unrollRun_decode {M : Model} {hc : v.caller.isData = true} {n : Nat} :
    (s : State v) → (sts : List (UnrollStep v n)) → (xs : List (Input v)) → UnrollRun L T M hc s sts xs →
    sts.mapM (·.decode M L hc) = some xs
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim
  | s, st :: sts, x :: xs, ⟨hd, _, h⟩ => by
    simp only [List.mapM_cons, hd, unrollRun_decode _ sts xs h]; rfl

/-- Goal soundness: in every model of generate's script for the target at depth `d` whose variables hold values of
their sorts, the steps decode to inputs whose run from the initial state answers at its last step in a class the
target aims at. So a found model always replays to its target; generate's check of that is never the one that fails. -/
theorem generate_sound (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {M : Model}
    {rules : RuleNames} {g : GenTarget} {d : Nat} {U : Unrolled v senv.nT}
    (hu : unroll L T P v senv d (genGoal L T rules g) = .ok U)
    (hM : ∀ n (h : n < U.ask.tys.length), VarSorted L U.ask.tys[n] (M.vars n)) (hA : ∀ a ∈ U.ask.asserts, Holds M a) :
    ∃ ys x, U.steps.mapM (·.decode M L chk.callerData) = some (ys ++ [x]) ∧
      Hits T v rules g x (step T v (run T v (Step.State.init v) ys).1 x) := by
  obtain ⟨xs, hrun⟩ := unroll_decode chk senv hu hM hA
  have hgoal : Holds M (genGoal L T rules g U.steps) := by
    simp only [unroll] at hu
    obtain ⟨S0, -, hu⟩ := bind_ok.1 hu
    obtain ⟨dts, -, hu⟩ := bind_ok.1 hu
    obtain ⟨vars, -, hu⟩ := bind_ok.1 hu
    cases pure_ok.1 hu
    exact hA _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hdec := unrollRun_decode _ _ _ hrun
  cases hx : xs.getLast? with
  | none =>
    obtain rfl := List.getLast?_eq_none_iff.1 hx
    cases hs : U.steps with
    | nil => simp [genGoal, hs, ff, Holds, Term.denote, Val.toBool] at hgoal
    | cons st sts => rw [hs] at hrun; exact hrun.elim
  | some x =>
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hx
    refine ⟨ys, x, hdec, ?_⟩
    obtain ⟨st, hlast, ⟨k, hk, hkd, hrel⟩, hno, -⟩ := unrollRun_last x ys _ _ hrun
    simp only [genGoal, hlast] at hgoal
    obtain ⟨k', hk', hh⟩ := (holds_takenT _ _).1 hgoal
    rw [hk] at hk'
    cases hk'
    exact kindHitT_sound hkd hrel hno hh

end

end Tazuna.Smt
