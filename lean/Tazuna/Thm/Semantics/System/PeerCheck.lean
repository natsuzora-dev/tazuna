import Tazuna.Semantics.Network
import Tazuna.Semantics.System.PeerCheck
import Tazuna.Thm.Data.Unify

namespace Tazuna.Thm.Semantics.System.PeerCheck

open Tazuna.Data Tazuna.Semantics Tazuna.Thm.Data.Trace Tazuna.Thm.Data.Unify Tazuna.Thm.Verify.Matching

variable {peerForm ownInputForm : String → Value → CValue} {service peer : String} {fromLines arrivals : List Nat}
  {lines peerLines : List TraceLine}

/-- The peer's createKey values, which the bindings bind. -/
abbrev createdOf (peerLines : List TraceLine) : List String := peerLines.flatMap (·.created.getD [])

/-- The peer's form of its value `x` of the definition `n`, with its peer keys turned back. -/
abbrev seenOf (peerForm : String → Value → CValue) (service : String) (lines : List TraceLine) (n : String)
    (x : Value) : CValue :=
  peerForm n (Bindings.rename ((peerKeys service lines).map fun (k, v) => (v, k)) x)

/--
Whether the scenario's value `y` of the peer's definition `n` stands for the peer's value `x` under the bindings `bs`:
in the forms that verify compares, `x` with its peer keys turned back into the run's createKey values matches `y` when
each createKey value of the peer stands for its binding (ValueMatches).
-/
def PeerSees (peerForm : String → Value → CValue) (service : String) (lines peerLines : List TraceLine) (bs : Bindings)
    (n : String) (x y : Value) : Prop :=
  ValueMatches (standsFor (createdOf peerLines) bs) (seenOf peerForm service lines n x) (peerForm n y)

/--
Whether the peer's line `b` emits the event `n`, at or before `time`, with a payload that `payload` stands for, as the
result of the request `resultOf` when it is given.
-/
def PeerEmits (peerForm : String → Value → CValue) (service : String) (lines peerLines : List TraceLine) (bs : Bindings)
    (n : String) (payload : Value) (resultOf : Option String) (time : DateTime) (b : TraceLine) : Prop :=
  ∃ id p r, b.body = .event .out id n p r ∧ (∀ q, resultOf = some q → r = some q) ∧
    b.time.time ≤ time.time ∧ PeerSees peerForm service lines peerLines bs n p payload

theorem peerLine_answer {bs bs' : Bindings} {i : Nat} {l : TraceLine} {id : String} {to target : String}
    {a : Answer} (hl : l.body = .answer .in id to a) (ht : peerTarget? peer lines to = some target)
    (hu : unreached lines to = false) (h : peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines bs i l = .ok bs') :
    ∃ t b, (answersTo (peerLines.take (peerBefore arrivals peerLines i)) .out to)[(answersTo (lines.take i) .in to).length]? =
        some (t, b) ∧ t.time ≤ l.time.time ∧ Unified (createdOf peerLines) bs bs'
          (fun f => AnswerCarries (fun x y => ValueMatches f (seenOf peerForm service lines target x)
            (peerForm target y)) b a) := by
  simp only [peerLine, hl, ht, hu, Bool.false_eq_true, ite_false] at h
  split at h
  · cases h
  · split at h
    · cases h
    · next t b hb =>
      split at h
      · next bs'' hs =>
        cases h
        split at hs
        · next htime => exact ⟨t, b, hb, htime, unifyAnswer_sound hs⟩
        · cases hs
      · cases h
      · cases h

theorem getElem?_take_some {α : Type} {xs : List α} {n j : Nat} {x : α} (h : (xs.take n)[j]? = some x) :
    j < n ∧ xs[j]? = some x := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem peerLine_event {bs bs' : Bindings} {i : Nat} {l : TraceLine} {id : String} {name n : String}
    {payload : Value} {resultOf : Option String} (hl : l.body = .event .in id name payload resultOf)
    (hn : peerName? peer name = some n) (h : peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines bs i l = .ok bs') :
    ∃ j b, peerLines[j]? = some b ∧ j < peerBefore arrivals peerLines i ∧ ∃ id' p r, b.body = .event .out id' n p r ∧
      (∀ q, resultOf = some q → r = some q) ∧ b.time.time ≤ l.time.time ∧
      Unified (createdOf peerLines) bs bs' (fun f => ValueMatches f (seenOf peerForm service lines n p) (peerForm n payload)) := by
  simp only [peerLine, hl, hn] at h
  split at h
  · next bs'' hf =>
    cases h
    obtain ⟨x, hx, hs⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨b, hb, hbx⟩ := List.mem_filterMap.mp hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
    split at hbx
    · next id' m p r hbody =>
      split at hbx
      · next hc =>
        cases hbx
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.all_eq_true] at hc
        obtain ⟨⟨rfl, htime⟩, hr⟩ := hc
        obtain ⟨hj, hb⟩ := getElem?_take_some hj
        cases hu : unify (createdOf peerLines) (seenOf peerForm service lines m p) (peerForm m payload) bs with
        | error => simp [hu, Except.toOption] at hs
        | ok b' =>
          simp only [hu, Except.toOption, Option.some.injEq] at hs
          subst hs
          exact ⟨j, b, hb, hj, id', p, r, hbody, fun q hq => by simpa using hr q hq,
            htime, (unify_sound _).1 _ _ _ _ hu⟩
      · cases hbx
    · cases hbx
  · cases h

theorem requestOf_id {d : Dir} {b : TraceLine.Body} {t id name : String} {x : Value}
    (h : requestOf? d b = some (t, id, name, x)) : b.id = id := by
  unfold requestOf? at h
  split at h <;> first | (split at h <;> simp_all [TraceLine.Body.id]) | cases h

/-- What the peer's line `b` that sends the scenario's from line `l` (sentAs?) gives, from the bindings `bs` to `bs'`. -/
structure SentAs (c : List String) (seen form : String → Value → CValue) (service : String) (bs bs' : Bindings)
    (l b : TraceLine) : Prop where
  time : b.time.time ≤ l.time.time
  fresh : bs.lookup b.body.id = none
  bound : bs'.lookup b.body.id = some l.body.id
  grows : bs <+: bs'
  oneToOne : OneToOne bs → OneToOne bs'
  body : (∃ t id name x id' m y, requestOf? .in l.body = some (t, id, name, x) ∧
      requestOf? .out b.body = some (t, id', m, y) ∧ peerName? service m = some name ∧
      ∀ R, bs' <+: R → ValueMatches (standsFor c R) (seen name y) (form name x)) ∨
    (∃ id to id' to', l.body = .unsubscribe .in id to ∧ b.body = .unsubscribe .out id' to' ∧ bs.lookup to' = some to)

theorem sentAs_spec {c : List String} {seen form : String → Value → CValue} {service : String} {bs bs' : Bindings}
    {l b : TraceLine} (h : sentAs? c seen form service bs l b = some (.ok bs')) :
    SentAs c seen form service bs bs' l b := by
  unfold sentAs? at h
  split at h
  · cases h
  · next htime =>
    have htime : b.time.time ≤ l.time.time := Int.not_lt.mp htime
    split at h
    · next id to id' to' hl hb =>
      split at h
      · next hto =>
        obtain ⟨b1, hb1, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        obtain ⟨hbind, hfresh⟩ := bindNew_bind hb1
        obtain ⟨hp, hlk, ho⟩ := bind_spec hbind
        simp only [beq_iff_eq] at hto
        exact ⟨htime, by simpa [hb, TraceLine.Body.id] using hfresh,
          by simpa [hb, hl, TraceLine.Body.id] using hlk, hp, ho, .inr ⟨id, to, id', to', hl, hb, hto⟩⟩
      · cases h
    · next lb bb hne =>
      split at h
      · next t id name x t' id' m y hx hy =>
        split at h
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, hm⟩ := hc
          obtain ⟨b1, hb1, hu⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hbind, hfresh⟩ := bindNew_bind hb1
          obtain ⟨hp, hlk, ho⟩ := bind_spec hbind
          have hU := (unify_sound c).1 _ _ _ _ hu
          have hid := requestOf_id hx
          have hid' := requestOf_id hy
          refine ⟨htime, by rw [hid']; exact hfresh, ?_, hp.trans hU.grows, fun h1 => hU.oneToOne (ho h1),
            .inl ⟨_, id, name, x, id', m, y, hx, hy, hm, fun R hR => hU.sound R hR⟩⟩
          rw [hid', hid]
          exact lookup_prefix hU.grows hlk
        · cases h
      · cases h

theorem peerSent_spec {c : List String} {seen form : String → Value → CValue} {service : String} {bs bs' : Bindings}
    {before : List TraceLine} {l : TraceLine} {j : Nat} (h : peerSent c seen form service bs before l = .ok (j, bs')) :
    ∃ b, before[j]? = some b ∧ SentAs c seen form service bs bs' l b := by
  unfold peerSent at h
  dsimp only at h
  split at h
  · next p hf =>
    cases h
    obtain ⟨⟨j', r⟩, hx, hs⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨⟨b, j''⟩, hb, hbx⟩ := List.mem_filterMap.mp hx
    obtain ⟨r', hr', he⟩ := Option.map_eq_some_iff.mp hbx
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    cases r' with
    | error => simp [Except.toOption] at hs
    | ok b' =>
      simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨b, List.mk_mem_zipIdx_iff_getElem?.mp hb, sentAs_spec hr'⟩
  · cases h

/-- The scenario's form of the peer's input `x` of a request to the definition `n` of `service`, its peer keys turned back. -/
abbrev seenInputOf (ownInputForm : String → Value → CValue) (service : String) (lines : List TraceLine) (n : String)
    (x : Value) : CValue :=
  ownInputForm n (Bindings.rename ((peerKeys service lines).map fun (k, v) => (v, k)) x)

/-- The check of a line that is neither an `in` answer nor an `in` event keeps the bindings or pairs a from line. -/
theorem peerLine_sent {bs bs' : Bindings} {i : Nat} {l : TraceLine}
    (ha : ∀ id to a, l.body ≠ .answer .in id to a) (he : ∀ id name p r, l.body ≠ .event .in id name p r)
    (h : peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines bs i l = .ok bs') :
    bs' = bs ∨ (fromLines.contains i ∧ ∃ j, peerSent (createdOf peerLines) (seenInputOf ownInputForm service lines)
      ownInputForm service bs (peerLines.take (peerBefore arrivals peerLines i)) l = .ok (j, bs')) := by
  unfold peerLine at h
  dsimp only at h
  split at h
  · next hb => exact absurd hb (ha _ _ _)
  · next hb => exact absurd hb (he _ _ _ _)
  all_goals first
    | (cases h; exact .inl rfl)
    | (split at h
       · next hc =>
         split at h
         · next j b hs => cases h; exact .inr ⟨hc, j, hs⟩
         · cases h
         · cases h
       · cases h; exact .inl rfl)

theorem peerLine_grows {bs bs' : Bindings} {i : Nat} {l : TraceLine}
    (h : peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines bs i l = .ok bs') :
    bs <+: bs' ∧ (OneToOne bs → OneToOne bs') := by
  cases hb : l.body with
  | answer d _ to a =>
    cases d with
    | out => simp [peerLine, hb] at h; subst h; exact ⟨List.prefix_refl _, id⟩
    | «in» =>
      cases ht : peerTarget? peer lines to with
      | none => simp [peerLine, hb, ht] at h; subst h; exact ⟨List.prefix_refl _, id⟩
      | some target =>
        cases hu : unreached lines to with
        | true => simp [peerLine, hb, ht, hu] at h; subst h; exact ⟨List.prefix_refl _, id⟩
        | false =>
          obtain ⟨_, _, _, _, hU⟩ := peerLine_answer hb ht hu h
          exact ⟨hU.grows, hU.oneToOne⟩
  | event d _ name payload resultOf =>
    cases d with
    | out => simp [peerLine, hb] at h; subst h; exact ⟨List.prefix_refl _, id⟩
    | «in» =>
      cases hn : peerName? peer name with
      | none => simp [peerLine, hb, hn] at h; subst h; exact ⟨List.prefix_refl _, id⟩
      | some n =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hU⟩ := peerLine_event hb hn h
        exact ⟨hU.grows, hU.oneToOne⟩
  | _ =>
    rcases peerLine_sent (by simp [hb]) (by simp [hb]) h with rfl | ⟨-, j, hs⟩
    · exact ⟨List.prefix_refl _, id⟩
    · obtain ⟨_, -, hS⟩ := peerSent_spec hs
      exact ⟨hS.grows, hS.oneToOne⟩

theorem peerBindings_succ {i : Nat} {l : TraceLine} (hi : lines[i]? = some l) :
    peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1) =
      (peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i) i l).toOption.getD
        (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i) := by
  have hz : lines.zipIdx[i]? = some (l, i) := by simp [List.getElem?_zipIdx, hi]
  simp only [peerBindings, List.take_add_one, List.foldl_append, hz]
  rfl

theorem peerBindings_grows (i : Nat) :
    peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i <+: peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1) ∧
      (OneToOne (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i) →
        OneToOne (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1))) := by
  cases hi : lines[i]? with
  | none =>
    have hz : lines.zipIdx[i]? = none := by simp [List.getElem?_zipIdx, hi]
    have he : peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1) =
        peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i := by
      simp only [peerBindings, List.take_add_one, List.foldl_append, hz]
      rfl
    rw [he]
    exact ⟨List.prefix_refl _, id⟩
  | some l =>
    rw [peerBindings_succ hi]
    cases h : peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i) i l with
    | error _ => exact ⟨List.prefix_refl _, id⟩
    | ok bs' => exact peerLine_grows h

theorem peerBindings_prefix {i j : Nat} (h : i ≤ j) :
    peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i <+: peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact (ih (by omega)).trans (peerBindings_grows (i + k)).1

/-- The bindings that the check builds are one-to-one. -/
theorem peerBindings_oneToOne (n : Nat) : OneToOne (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines n) := by
  induction n with
  | zero => simp [peerBindings, OneToOne]
  | succ n ih => exact (peerBindings_grows n).2 ih

/-- No violation means that the peer's run of the derived inputs did not halt. -/
theorem peerFindings_halted {halted : Option (PeerOrigin × String)}
    (h : peerFindings peerForm ownInputForm service peer fromLines arrivals lines peerLines halted = []) : halted = none := by
  cases halted with
  | none => rfl
  | some p => simp [peerFindings] at h

theorem peerLine_ok {halted : Option (PeerOrigin × String)} {i : Nat} {l : TraceLine}
    (h : peerFindings peerForm ownInputForm service peer fromLines arrivals lines peerLines halted = []) (hi : lines[i]? = some l) :
    peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i) i l =
      .ok (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1)) := by
  cases peerFindings_halted h
  simp only [peerFindings] at h
  have hz : (l, i) ∈ lines.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  have := List.filterMap_eq_nil_iff.mp h _ hz
  rw [peerBindings_succ hi]
  split at this
  · cases this
  · next bs' hb => rw [hb]; rfl

/-- The bindings after the whole run: the one renaming under which the stage 1 theorems hold. -/
abbrev peerFinal (peerForm ownInputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (lines peerLines : List TraceLine) : Bindings :=
  peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines lines.length

theorem final_of {i : Nat} {l : TraceLine} (hi : lines[i]? = some l) :
    peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1) <+: peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines :=
  peerBindings_prefix (List.getElem?_eq_some_iff.mp hi).1

/--
Stage 1 for answers: with no violation, each answer that a mock gives to a request to the peer that reached it is the
peer's answer to the request at the same place, the k-th answer to it when the mock is the k-th, as the scenario sees
the peer's values under the final bindings (PeerSees), and the peer gives it at or before the mock's time, before it
takes an input that arrives after the mock (peerBefore).
-/
theorem mocked_answer_given {halted : Option (PeerOrigin × String)} {i : Nat} {l : TraceLine} {id : String}
    {to target : String} {a : Answer}
    (h : peerFindings peerForm ownInputForm service peer fromLines arrivals lines peerLines halted = []) (hi : lines[i]? = some l)
    (hl : l.body = .answer .in id to a) (ht : peerTarget? peer lines to = some target)
    (hu : unreached lines to = false) :
    ∃ t b, (answersTo (peerLines.take (peerBefore arrivals peerLines i)) .out to)[(answersTo (lines.take i) .in to).length]? =
        some (t, b) ∧
      AnswerCarries (PeerSees peerForm service lines peerLines (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines) target) b a ∧
        t.time ≤ l.time.time := by
  obtain ⟨t, b, hb, htime, hU⟩ := peerLine_answer hl ht hu (peerLine_ok h hi)
  exact ⟨t, b, hb, hU.sound _ (final_of hi), htime⟩

theorem answersTo_take_getElem? {lines : List TraceLine} {n k : Nat} {d : Dir} {to : String} {x : DateTime × Answer}
    (h : (answersTo (lines.take n) d to)[k]? = some x) : (answersTo lines d to)[k]? = some x := by
  have e : answersTo lines d to = answersTo (lines.take n) d to ++ answersTo (lines.drop n) d to := by
    simp only [answersTo, ← List.filterMap_append, List.take_append_drop]
  rw [e, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem filterMap_getElem? {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (k : Nat) (y : β), (xs.filterMap f)[k]? = some y →
      ∃ i x, xs[i]? = some x ∧ f x = some y ∧ ((xs.take i).filterMap f).length = k
  | [], _, _, h => by simp at h
  | x :: xs, k, y, h => by
    rw [List.filterMap_cons] at h
    cases hf : f x with
    | none =>
      rw [hf] at h
      obtain ⟨i, z, hz, hfz, hl⟩ := filterMap_getElem? f xs k y h
      exact ⟨i + 1, z, by simpa using hz, hfz, by simp [hf, hl]⟩
    | some b =>
      rw [hf] at h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, x, rfl, by rw [hf, h], by simp⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨i, z, hz, hfz, hl⟩ := filterMap_getElem? f xs k y h
        exact ⟨i + 1, z, by simpa using hz, hfz, by simp [hf, hl]⟩

/-- The k-th answer in direction `dir` to `to` is the answer of a line that k such answers come before. -/
theorem answersTo_getElem? {lines : List TraceLine} {dir : Dir} {to : String} {k : Nat} {t : DateTime} {a : Answer}
    (h : (answersTo lines dir to)[k]? = some (t, a)) :
    ∃ i l id, lines[i]? = some l ∧ l.body = .answer dir id to a ∧ l.time = t ∧
      (answersTo (lines.take i) dir to).length = k := by
  obtain ⟨i, l, hl, hf, hk⟩ := filterMap_getElem? _ lines k (t, a) h
  refine ⟨i, l, ?_⟩
  split at hf
  · next d id' to' a' hb =>
    split at hf
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨id', hl, hb, rfl, hk⟩
    · simp at hf
  · simp at hf

/--
Stage 1 for subscriptions and every other request: with no violation, the answers that mocks give to a request to the
peer that reached it are, in order and as the scenario sees the peer's values under the final bindings (PeerSees), a
prefix of the peer's answers to the request, each given at or before the mock's time.
-/
theorem mocked_answers_prefix {halted : Option (PeerOrigin × String)} {to target : String} {k : Nat} {t : DateTime}
    {a : Answer} (h : peerFindings peerForm ownInputForm service peer fromLines arrivals lines peerLines halted = [])
    (ht : peerTarget? peer lines to = some target)
    (hu : unreached lines to = false) (hk : (answersTo lines .in to)[k]? = some (t, a)) :
    ∃ t' b, (answersTo peerLines .out to)[k]? = some (t', b) ∧
      AnswerCarries (PeerSees peerForm service lines peerLines (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines) target) b a ∧
        t'.time ≤ t.time := by
  obtain ⟨i, l, id, hi, hl, rfl, rfl⟩ := answersTo_getElem? hk
  obtain ⟨t', b, hb, hc, hle⟩ := mocked_answer_given h hi hl ht hu
  exact ⟨t', b, answersTo_take_getElem? hb, hc, hle⟩

/--
Stage 1 for events: with no violation, the peer emits each event of the peer that the scenario receives, at or before
the time the scenario receives it, with a payload that the scenario's stands for under the final bindings, as the
result of the request that the scenario names as its result (PeerEmits), and before it takes an input that arrives
after the scenario's line (peerBefore).
Two deliveries of one event may name the same line of the peer.
-/
theorem received_event_emitted {halted : Option (PeerOrigin × String)} {i : Nat} {l : TraceLine} {id : String}
    {name n : String} {payload : Value} {resultOf : Option String}
    (h : peerFindings peerForm ownInputForm service peer fromLines arrivals lines peerLines halted = []) (hi : lines[i]? = some l)
    (hl : l.body = .event .in id name payload resultOf) (hn : peerName? peer name = some n) :
    ∃ j b, peerLines[j]? = some b ∧ j < peerBefore arrivals peerLines i ∧
      PeerEmits peerForm service lines peerLines (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines) n payload resultOf l.time b := by
  obtain ⟨j, b, hb, hj, id', p, r, hbody, hr, htime, hU⟩ := peerLine_event hl hn (peerLine_ok h hi)
  exact ⟨j, b, hb, hj, id', p, r, hbody, hr, htime, hU.sound _ (final_of hi)⟩

end Tazuna.Thm.Semantics.System.PeerCheck
