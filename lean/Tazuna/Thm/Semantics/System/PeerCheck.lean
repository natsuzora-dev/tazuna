import Tazuna.Semantics.System.PeerCheck
import Tazuna.Thm.Data.Unify
import Tazuna.Thm.Semantics.System.Peer

namespace Tazuna.Thm.Semantics.System.PeerCheck

open Tazuna.Data Tazuna.Semantics Tazuna.Thm.Data.Trace Tazuna.Thm.Data.Unify Tazuna.Thm.Semantics.System.Peer
  Tazuna.Thm.Verify.Matching

variable {service : String} {d : PeerDerivation} {arrivals : List Nat}
  {lines peerLines : List TraceLine}

/-- The peer's createKey values, which the bindings bind. -/
abbrev createdOf (peerLines : List TraceLine) : List String := peerLines.flatMap (·.created.getD [])

/-- The peer's form of its value `x` of the definition `n`, with its peer keys turned back. -/
abbrev seenOf (peerForm : NamedForm) (service : String) (lines : List TraceLine) (n : String)
    (x : Value) : CValue :=
  peerForm n (Bindings.rename ((peerKeys service lines).map fun (k, v) => (v, k)) x)

/--
Whether the scenario's value `y` of the peer's definition `n` stands for the peer's value `x` under the bindings `bs`:
in the forms that verify compares, `x` with its peer keys turned back into the run's createKey values matches `y` when
each createKey value of the peer stands for its binding (ValueMatches).
-/
def PeerSees (peerForm : NamedForm) (service : String) (lines peerLines : List TraceLine) (bs : Bindings)
    (n : String) (x y : Value) : Prop :=
  ValueMatches (standsFor (createdOf peerLines) bs) (seenOf peerForm service lines n x) (peerForm n y)

/--
Whether the peer's line `b` emits the event `n`, at or before `time`, with a payload that `payload` stands for, as the
result of the request `resultOf` when it is given.
-/
def PeerEmits (peerForm : NamedForm) (service : String) (lines peerLines : List TraceLine) (bs : Bindings)
    (n : String) (payload : Value) (resultOf : Option String) (time : DateTime) (b : TraceLine) : Prop :=
  ∃ id p r, b.body = .event .out id n p r ∧ (∀ q, resultOf = some q → r = some q) ∧
    b.time.time ≤ time.time ∧ PeerSees peerForm service lines peerLines bs n p payload

theorem peerLine_answer {bs bs' : Bindings} {i : Nat} {l : TraceLine} {id : String} {to target : String}
    {a : Answer} (hl : l.body = .answer .in id to a) (ht : peerTarget? d.peer lines to = some target)
    (hu : unreached lines to = false) (h : peerLine service d arrivals lines peerLines bs i l = .ok bs') :
    ∃ t b, (answersTo (peerLines.take (peerBefore arrivals peerLines i)) .out to)[(answersTo (lines.take i) .in to).length]? =
        some (t, b) ∧ t.time ≤ l.time.time ∧ Unified (createdOf peerLines) bs bs'
          (fun f => AnswerCarries (fun x y => ValueMatches f (seenOf d.peerForm service lines target x)
            (d.peerForm target y)) b a) := by
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
    (hn : peerName? d.peer name = some n) (h : peerLine service d arrivals lines peerLines bs i l = .ok bs') :
    ∃ j b, peerLines[j]? = some b ∧ j < peerBefore arrivals peerLines i ∧ ∃ id' p r, b.body = .event .out id' n p r ∧
      (∀ q, resultOf = some q → r = some q) ∧ b.time.time ≤ l.time.time ∧
      Unified (createdOf peerLines) bs bs' (fun f => ValueMatches f (seenOf d.peerForm service lines n p) (d.peerForm n payload)) := by
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
        cases hu : unify (createdOf peerLines) (seenOf d.peerForm service lines m p) (d.peerForm m payload) bs with
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
structure SentAs (c : List String) (seen form : NamedForm) (service : String) (bs bs' : Bindings)
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

theorem sentAs_spec {c : List String} {seen form : NamedForm} {service : String} {bs bs' : Bindings}
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

theorem peerSent_spec {c : List String} {seen form : NamedForm} {service : String} {bs bs' : Bindings}
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
abbrev seenInputOf (ownInputForm : NamedForm) (service : String) (lines : List TraceLine) (n : String)
    (x : Value) : CValue :=
  ownInputForm n (Bindings.rename ((peerKeys service lines).map fun (k, v) => (v, k)) x)

/-- The check of a line that is neither an `in` answer nor an `in` event keeps the bindings or pairs a from line. -/
theorem peerLine_sent {bs bs' : Bindings} {i : Nat} {l : TraceLine}
    (ha : ∀ id to a, l.body ≠ .answer .in id to a) (he : ∀ id name p r, l.body ≠ .event .in id name p r)
    (h : peerLine service d arrivals lines peerLines bs i l = .ok bs') :
    bs' = bs ∨ (d.fromLines.contains i ∧ ∃ j, peerSent (createdOf peerLines) (seenInputOf d.ownInputForm service lines)
      d.ownInputForm service bs (peerLines.take (peerBefore arrivals peerLines i)) l = .ok (j, bs')) := by
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
    (h : peerLine service d arrivals lines peerLines bs i l = .ok bs') :
    bs <+: bs' ∧ (OneToOne bs → OneToOne bs') := by
  cases hb : l.body with
  | answer d _ to a =>
    cases d with
    | out => simp [peerLine, hb] at h; subst h; exact ⟨List.prefix_refl _, id⟩
    | «in» =>
      cases ht : peerTarget? d.peer lines to with
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
      cases hn : peerName? d.peer name with
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
    peerBindings service d arrivals lines peerLines (i + 1) =
      (peerLine service d arrivals lines peerLines (peerBindings service d arrivals lines peerLines i) i l).toOption.getD
        (peerBindings service d arrivals lines peerLines i) := by
  have hz : lines.zipIdx[i]? = some (l, i) := by simp [List.getElem?_zipIdx, hi]
  simp only [peerBindings, List.take_add_one, List.foldl_append, hz]
  rfl

theorem peerBindings_grows (i : Nat) :
    peerBindings service d arrivals lines peerLines i <+: peerBindings service d arrivals lines peerLines (i + 1) ∧
      (OneToOne (peerBindings service d arrivals lines peerLines i) →
        OneToOne (peerBindings service d arrivals lines peerLines (i + 1))) := by
  cases hi : lines[i]? with
  | none =>
    have hz : lines.zipIdx[i]? = none := by simp [List.getElem?_zipIdx, hi]
    have he : peerBindings service d arrivals lines peerLines (i + 1) =
        peerBindings service d arrivals lines peerLines i := by
      simp only [peerBindings, List.take_add_one, List.foldl_append, hz]
      rfl
    rw [he]
    exact ⟨List.prefix_refl _, id⟩
  | some l =>
    rw [peerBindings_succ hi]
    cases h : peerLine service d arrivals lines peerLines (peerBindings service d arrivals lines peerLines i) i l with
    | error _ => exact ⟨List.prefix_refl _, id⟩
    | ok bs' => exact peerLine_grows h

theorem peerBindings_prefix {i j : Nat} (h : i ≤ j) :
    peerBindings service d arrivals lines peerLines i <+: peerBindings service d arrivals lines peerLines j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact (ih (by omega)).trans (peerBindings_grows (i + k)).1

/-- The bindings that the check builds are one-to-one. -/
theorem peerBindings_oneToOne (n : Nat) : OneToOne (peerBindings service d arrivals lines peerLines n) := by
  induction n with
  | zero => simp [peerBindings, OneToOne]
  | succ n ih => exact (peerBindings_grows n).2 ih

/-- No violation means that the peer's run of the derived inputs did not halt. -/
theorem peerFindings_halted {halted : Option (PeerOrigin × String)}
    (h : peerFindings service d arrivals lines peerLines halted = []) : halted = none := by
  cases halted with
  | none => rfl
  | some p => simp [peerFindings] at h

theorem peerLine_ok {halted : Option (PeerOrigin × String)} {i : Nat} {l : TraceLine}
    (h : peerFindings service d arrivals lines peerLines halted = []) (hi : lines[i]? = some l) :
    peerLine service d arrivals lines peerLines (peerBindings service d arrivals lines peerLines i) i l =
      .ok (peerBindings service d arrivals lines peerLines (i + 1)) := by
  cases peerFindings_halted h
  simp only [peerFindings] at h
  have hz : (l, i) ∈ lines.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  have := List.filterMap_eq_nil_iff.mp h _ hz
  rw [peerBindings_succ hi]
  split at this
  · cases this
  · next bs' hb => rw [hb]; rfl

/-- The bindings after the whole run: the one renaming under which the stage 1 theorems hold. -/
abbrev peerFinal (service : String) (d : PeerDerivation) (arrivals : List Nat)
    (lines peerLines : List TraceLine) : Bindings :=
  peerBindings service d arrivals lines peerLines lines.length

theorem final_of {i : Nat} {l : TraceLine} (hi : lines[i]? = some l) :
    peerBindings service d arrivals lines peerLines (i + 1) <+: peerFinal service d arrivals lines peerLines :=
  peerBindings_prefix (List.getElem?_eq_some_iff.mp hi).1

/--
Stage 1 for answers: with no violation, each answer that a mock gives to a request to the peer that reached it is the
peer's answer to the request at the same place, the k-th answer to it when the mock is the k-th, as the scenario sees
the peer's values under the final bindings (PeerSees), and the peer gives it at or before the mock's time, before it
takes an input that arrives after the mock (peerBefore).
-/
theorem mocked_answer_given {halted : Option (PeerOrigin × String)} {i : Nat} {l : TraceLine} {id : String}
    {to target : String} {a : Answer}
    (h : peerFindings service d arrivals lines peerLines halted = []) (hi : lines[i]? = some l)
    (hl : l.body = .answer .in id to a) (ht : peerTarget? d.peer lines to = some target)
    (hu : unreached lines to = false) :
    ∃ t b, (answersTo (peerLines.take (peerBefore arrivals peerLines i)) .out to)[(answersTo (lines.take i) .in to).length]? =
        some (t, b) ∧
      AnswerCarries (PeerSees d.peerForm service lines peerLines (peerFinal service d arrivals lines peerLines) target) b a ∧
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
    {a : Answer} (h : peerFindings service d arrivals lines peerLines halted = [])
    (ht : peerTarget? d.peer lines to = some target)
    (hu : unreached lines to = false) (hk : (answersTo lines .in to)[k]? = some (t, a)) :
    ∃ t' b, (answersTo peerLines .out to)[k]? = some (t', b) ∧
      AnswerCarries (PeerSees d.peerForm service lines peerLines (peerFinal service d arrivals lines peerLines) target) b a ∧
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
    (h : peerFindings service d arrivals lines peerLines halted = []) (hi : lines[i]? = some l)
    (hl : l.body = .event .in id name payload resultOf) (hn : peerName? d.peer name = some n) :
    ∃ j b, peerLines[j]? = some b ∧ j < peerBefore arrivals peerLines i ∧
      PeerEmits d.peerForm service lines peerLines (peerFinal service d arrivals lines peerLines) n payload resultOf l.time b := by
  obtain ⟨j, b, hb, hj, id', p, r, hbody, hr, htime, hU⟩ := peerLine_event hl hn (peerLine_ok h hi)
  exact ⟨j, b, hb, hj, id', p, r, hbody, hr, htime, hU.sound _ (final_of hi)⟩

theorem answersTo_append (xs ys : List TraceLine) (d : Dir) (to : String) :
    answersTo (xs ++ ys) d to = answersTo xs d to ++ answersTo ys d to := by
  simp [answersTo, List.filterMap_append]

theorem answersTo_take_succ {lines : List TraceLine} {i : Nat} {l : TraceLine} {d : Dir} {id : String}
    {to : String} {a : Answer} (hi : lines[i]? = some l) (hl : l.body = .answer d id to a) :
    answersTo (lines.take (i + 1)) d to = answersTo (lines.take i) d to ++ [(l.time, a)] := by
  rw [List.take_add_one, hi, answersTo_append]
  simp [answersTo, hl]

theorem answersTo_take_mono {lines : List TraceLine} {d : Dir} {to : String} {j j' : Nat} (h : j' ≤ j) :
    (answersTo (lines.take j') d to).length ≤ (answersTo (lines.take j) d to).length := by
  have e : lines.take j' = (lines.take j).take j' := by rw [List.take_take, Nat.min_eq_left h]
  rw [e]
  conv => rhs; rw [← List.take_append_drop j' (lines.take j)]
  rw [answersTo_append, List.length_append]
  omega

theorem answersTo_take_lt {lines : List TraceLine} {i i' : Nat} {l : TraceLine} {d : Dir} {id : String}
    {to : String} {a : Answer} (hi : lines[i]? = some l) (hl : l.body = .answer d id to a) (h : i < i') :
    (answersTo (lines.take i) d to).length < (answersTo (lines.take i') d to).length := by
  have := answersTo_take_mono (lines := lines) (d := d) (to := to) (Nat.succ_le_of_lt h)
  rw [answersTo_take_succ hi hl, List.length_append] at this
  simp at this
  omega

theorem answersTo_at {lines : List TraceLine} {j : Nat} {l : TraceLine} {d : Dir} {id : String} {to : String}
    {b : Answer} (hj : lines[j]? = some l) (hl : l.body = .answer d id to b) :
    (answersTo lines d to)[(answersTo (lines.take j) d to).length]? = some (l.time, b) := by
  rw [show answersTo lines d to = answersTo (lines.take (j + 1)) d to ++ answersTo (lines.drop (j + 1)) d to by
    rw [← answersTo_append, List.take_append_drop], answersTo_take_succ hj hl, List.append_assoc,
    List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Line `j` of `lines` is the `k`-th answer in direction `d` to the request `to`. -/
def AnswerAt (lines : List TraceLine) (d : Dir) (to : String) (k j : Nat) : Prop :=
  ∃ l id b, lines[j]? = some l ∧ l.body = .answer d id to b ∧ (answersTo (lines.take j) d to).length = k

theorem answerAt_lt {lines : List TraceLine} {d : Dir} {to : String} {k k' j j' : Nat} (h : AnswerAt lines d to k j)
    (h' : AnswerAt lines d to k' j') (hk : k < k') : j < j' := by
  obtain ⟨_, _, _, _, _, rfl⟩ := h
  obtain ⟨_, _, _, _, _, rfl⟩ := h'
  apply Nat.lt_of_not_le
  intro hle
  have := answersTo_take_mono (lines := lines) (d := d) (to := to) hle
  omega

theorem answerAt_same {lines : List TraceLine} {d : Dir} {to to' : String} {k k' j : Nat}
    (h : AnswerAt lines d to k j) (h' : AnswerAt lines d to' k' j) : to' = to ∧ k' = k := by
  obtain ⟨l, id, b, hj, hl, rfl⟩ := h
  obtain ⟨l', id', b', hj', hl', rfl⟩ := h'
  rw [hj] at hj'
  cases hj'
  rw [hl] at hl'
  cases hl'
  exact ⟨rfl, rfl⟩

theorem mem_peerInputs_line {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} {st : Step} {i : Nat}
    (h : (st, PeerOrigin.line i) ∈ peerInputs service d lines peerLines) :
    ∃ l b, lines[i]? = some l ∧
      peerInput? service d.peer d.received d.fromLines lines (peerForward service d (peerArrivals service d lines) lines peerLines i) l = some b ∧
      st = ⟨l.time, b, none, none, none⟩ := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ⟨_, _, he⟩ | ⟨a, ⟨n, _, ha⟩, he⟩
  · simp at he
  · rcases ha with ⟨_, _, rfl⟩ | ha
    · simp at he
    · cases hl : lines[n]? with
      | none => simp [hl] at ha
      | some l =>
        simp only [hl, Option.mem_toList, Option.map_eq_some_iff] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        simp only [Prod.mk.injEq, PeerOrigin.line.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨l, b, hl, hb, rfl⟩

theorem peerInputs_line_mem {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} {i : Nat} {l : TraceLine}
    {b : Step.Body} (hi : lines[i]? = some l)
    (hb : peerBody? d.peer lines (peerForward service d (peerArrivals service d lines) lines peerLines i) l = some b) :
    (⟨l.time, b, none, none, none⟩, PeerOrigin.line i) ∈
      peerInputs service d lines peerLines := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap]
  refine .inr ⟨(⟨l.time, b, none, none, none⟩, PeerOrigin.line i), ⟨i, ?_, .inr ?_⟩, rfl⟩
  · have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.mem_range]
    omega
  · simp [hi, hb, peerInput?]

theorem peerInputs_lines_pairwise {service : String} {d : PeerDerivation}
    {lines peerLines : List TraceLine} :
    ((peerInputs service d lines peerLines).filterMap
      (·.2.line?)).Pairwise (· < ·) := by
  have hnone : ∀ {α : Type} (l : List α), l.filterMap (fun _ => (none : Option Nat)) = [] :=
    fun _ => List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
  simp only [peerInputs, peerPlaced, List.filterMap_append, List.filterMap_map, List.filterMap_flatMap, Function.comp_def,
    PeerOrigin.line?, hnone, List.nil_append]
  refine pairwise_flatMap_single List.pairwise_lt_range (fun n m hm => ?_) (fun n => ?_)
  · split at hm
    · simp only [Option.toList_map, List.filterMap_map, Function.comp_def, List.mem_filterMap] at hm
      obtain ⟨_, _, hm⟩ := hm
      simpa using hm.symm
    · simp at hm
  · split
    · simp only [Option.toList_map, List.filterMap_map, Function.comp_def]
      refine Nat.le_trans (List.length_filterMap_le _ _) ?_
      generalize (peerInput? _ _ _ _ _ _ _ : Option Step.Body) = o
      cases o <;> simp
    · simp

theorem peerInputs_lines_nodup {service : String} {d : PeerDerivation}
    {lines peerLines : List TraceLine} :
    ((peerInputs service d lines peerLines).filterMap
      (·.2.line?)).Nodup :=
  peerInputs_lines_pairwise.imp Nat.ne_of_lt

/-- The arrivals of the peer's inputs are those of peerArrivals. -/
theorem peerInputs_arrivals {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} :
    (peerInputs service d lines peerLines).map (·.2.arrival d.elsewhere) =
      peerArrivals service d lines := by
  have key : ∀ f g, (peerPlaced service d lines f).map (·.2.arrival d.elsewhere) =
      (peerPlaced service d lines g).map (·.2.arrival d.elsewhere) := fun f g => by
    have := congrArg (List.map (PeerOrigin.arrival d.elsewhere)) (peerPlaced_origins (service := service) (d := d)
      (lines := lines) f g)
    simpa only [List.map_map, Function.comp_def] using this
  simp only [peerInputs, peerArrivals, List.map_append, List.map_map]
  congr 1
  refine Eq.trans (List.map_congr_left fun ⟨_, o⟩ _ => ?_) (key _ _)
  cases o <;> rfl

theorem arrivals_of_line {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} {k n : Nat} {st : Step}
    (h : (peerInputs service d lines peerLines)[k]? = some (st, PeerOrigin.line n)) :
    (peerArrivals service d lines)[k]? = some n := by
  rw [← peerInputs_arrivals (d := d) (peerLines := peerLines), List.getElem?_map, h]
  rfl

/-- A line before peerBefore of the run's line `i` is a line of an input that arrives at or before `i`. -/
theorem arrival_le {arrivals : List Nat} {peerLines : List TraceLine} {i k j a : Nat} {l : TraceLine}
    (hlen : arrivals.length = (inLines peerLines).length) (hj : j < peerBefore arrivals peerLines i)
    (hk : (inLines peerLines)[k]? = some (l, j)) (ha : arrivals[k]? = some a) : a ≤ i := by
  unfold peerBefore at hj
  cases hf : arrivals.findIdx? (i < ·) with
  | none =>
    have := (List.findIdx?_eq_none_iff.mp hf) a (List.mem_of_getElem? ha)
    simp only [decide_eq_false_iff_not, Nat.not_lt] at this
    exact this
  | some k0 =>
    rw [hf] at hj
    obtain ⟨hk0, -, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    obtain ⟨⟨l0, p0⟩, h0⟩ : ∃ x, (inLines peerLines)[k0]? = some x :=
      ⟨_, List.getElem?_eq_getElem (hlen ▸ hk0)⟩
    simp only [h0, Option.map_some, Option.getD_some] at hj
    obtain ⟨hka, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    rcases Nat.lt_or_ge k k0 with hlt | hge
    · have := hmin k hlt
      simp only [decide_eq_true_eq, Nat.not_lt] at this
      exact this
    · have := inLines_le h0 hk hge
      omega

/-- peerBefore of a line before an input's arrival is at or before the input's `in` line. -/
theorem before_le {arrivals : List Nat} {peerLines : List TraceLine} {i k p a : Nat} {l : TraceLine}
    (hlen : arrivals.length = (inLines peerLines).length) (hk : (inLines peerLines)[k]? = some (l, p))
    (ha : arrivals[k]? = some a) (hi : i < a) : peerBefore arrivals peerLines i ≤ p := by
  unfold peerBefore
  cases hf : arrivals.findIdx? (i < ·) with
  | none =>
    have := (List.findIdx?_eq_none_iff.mp hf) a (List.mem_of_getElem? ha)
    simp only [decide_eq_false_iff_not] at this
    exact absurd hi this
  | some k0 =>
    obtain ⟨hk0, -, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    obtain ⟨⟨l0, p0⟩, h0⟩ : ∃ x, (inLines peerLines)[k0]? = some x :=
      ⟨_, List.getElem?_eq_getElem (hlen ▸ hk0)⟩
    simp only [h0, Option.map_some, Option.getD_some]
    obtain ⟨hka, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    rcases Nat.lt_or_ge k k0 with hlt | hge
    · have := hmin k hlt
      simp only [decide_eq_true_eq] at this
      exact absurd hi this
    · exact inLines_le h0 hk hge

theorem index_unique {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {k k' : Nat} {a a' : α} {b : β},
      (l.filterMap f).Nodup → l[k]? = some a → l[k']? = some a' → f a = some b → f a' = some b → k = k'
  | [], _, _, _, _, _, _, hk, _, _, _ => by simp at hk
  | _ :: _, 0, 0, _, _, _, _, _, _, _, _ => rfl
  | x :: xs, 0, k' + 1, a, a', b, hn, hk, hk', ha, ha' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    simp only [List.getElem?_cons_succ] at hk'
    subst hk
    rw [List.filterMap_cons_some ha, List.nodup_cons] at hn
    exact absurd (List.mem_filterMap.mpr ⟨a', List.mem_of_getElem? hk', ha'⟩) hn.1
  | x :: xs, k + 1, 0, a, a', b, hn, hk, hk', ha, ha' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
    simp only [List.getElem?_cons_succ] at hk
    subst hk'
    rw [List.filterMap_cons_some ha', List.nodup_cons] at hn
    exact absurd (List.mem_filterMap.mpr ⟨a, List.mem_of_getElem? hk, ha⟩) hn.1
  | x :: xs, k + 1, k' + 1, a, a', b, hn, hk, hk', ha, ha' => by
    have hn' : (xs.filterMap f).Nodup := hn.sublist ((List.sublist_cons_self x xs).filterMap f)
    exact congrArg (· + 1) (index_unique hn' hk hk' ha ha')

theorem peerInputs_line_unique {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} {k k' i : Nat}
    {x x' : Step} (hk : (peerInputs service d lines peerLines)[k]? = some (x, .line i))
    (hk' : (peerInputs service d lines peerLines)[k']? = some (x', .line i)) :
    k = k' :=
  index_unique (f := (·.2.line?)) peerInputs_lines_nodup hk hk' rfl rfl

theorem mem_peerInputs_given {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} {st : Step}
    (h : (st, PeerOrigin.given) ∈ peerInputs service d lines peerLines) : st ∈ d.state := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ⟨s, hs, he⟩ | ⟨a, ⟨n, _, ha⟩, he⟩
  · simp only [Prod.mk.injEq] at he
    exact he.1 ▸ hs
  · exfalso
    rcases ha with ⟨_, _, rfl⟩ | ha
    · simp at he
    · cases hl : lines[n]? with
      | none => simp [hl] at ha
      | some l =>
        simp only [hl, Option.mem_toList, Option.map_eq_some_iff] at ha
        obtain ⟨b, -, rfl⟩ := ha
        simp at he

theorem mem_peerInputs_elsewhere {service : String} {d : PeerDerivation} {lines peerLines : List TraceLine} {st : Step} {k : Nat}
    (h : (st, PeerOrigin.elsewhere k) ∈ peerInputs service d lines peerLines) :
    ∃ s ∈ d.elsewhere.map (·.2), ∃ keys, st.body = s.body.forPeer keys := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ⟨_, _, he⟩ | ⟨a, ⟨n, _, ha⟩, he⟩
  · simp at he
  · rcases ha with ⟨⟨⟨p, s⟩, j⟩, hm, rfl⟩ | ha
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp only [List.mem_filter] at hm
      exact ⟨s, List.mem_map.mpr ⟨(p, s), List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hm.1), rfl⟩, _,
        rfl⟩
    · cases hl : lines[n]? with
      | none => simp [hl] at ha
      | some l =>
        simp only [hl, Option.mem_toList, Option.map_eq_some_iff] at ha
        obtain ⟨b, -, rfl⟩ := ha
        simp at he

/-- A line that a from line pairs (SentAs) is an `in` request or end of a subscription. -/
theorem SentAs.request {c : List String} {seen form : NamedForm} {service : String}
    {bs bs' : Bindings} {l b : TraceLine} (h : SentAs c seen form service bs bs' l b) :
    l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      (∀ id name p r, l.body ≠ .event .in id name p r) ∧ b.body.dir = .out ∧ isEventLine b = false ∧
      (∀ id to a, b.body ≠ .answer .out id to a) := by
  rcases h.body with ⟨t, id, name, x, id', m, y, hx, hy, -, -⟩ | ⟨id, to, id', to', hl, hb⟩
  · rcases requestOf_some hx with ⟨hl, -⟩ | ⟨hl, -⟩ | ⟨hl, -⟩ <;>
    rcases requestOf_some hy with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;>
    simp [hl, hb, TraceLine.Body.dir, isEventLine]
  · simp [hl, hb, TraceLine.Body.dir, isEventLine]

/-- The check of a from line pairs it with the line that peerSent finds. -/
theorem peerLine_paired {bs bs' bs'' : Bindings} {i j : Nat} {l : TraceLine}
    (hc : d.fromLines.contains i = true)
    (hs : peerSent (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service bs
      (peerLines.take (peerBefore arrivals peerLines i)) l = .ok (j, bs'))
    (h : peerLine service d arrivals lines peerLines bs i l = .ok bs'') : bs'' = bs' := by
  obtain ⟨b, -, hS⟩ := peerSent_spec hs
  obtain ⟨-, ha, he, -⟩ := hS.request
  unfold peerLine at h
  dsimp only at h
  split at h
  · next hb => exact absurd hb (ha _ _ _)
  · next hb => exact absurd hb (he _ _ _ _)
  all_goals first
    | (split at h
       · split at h
         · next _ _ hs'' =>
           cases h
           have h3 := hs.symm.trans hs''
           simp only [Except.ok.injEq, Prod.mk.injEq] at h3
           exact h3.2.symm
         · next hs'' => cases hs.symm.trans hs''
         · next hs'' => cases hs.symm.trans hs''
       · next hn => exact absurd hc hn)
    | (rcases hS.body with ⟨_, _, _, _, _, _, _, hx, -⟩ | ⟨_, _, _, _, hl, -⟩
       · rcases requestOf_some hx with ⟨hl, -⟩ | ⟨hl, -⟩ | ⟨hl, -⟩ <;> simp_all
       · simp_all)

/-- The place in the peer's run of the line that sends the scenario's from line `i` (peerSent), if any. -/
def peerPaired? (service : String) (d : PeerDerivation) (arrivals : List Nat)
    (lines peerLines : List TraceLine) (i : Nat) : Option Nat :=
  if d.fromLines.contains i then
    (lines[i]?.bind fun l => (peerSent (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
      (peerBindings service d arrivals lines peerLines i)
      (peerLines.take (peerBefore arrivals peerLines i)) l).toOption).map (·.1)
  else none

/--
With no violation, the peer's line that sends the scenario's from line `i` comes before the peer takes an input that
arrives after the line, and the check binds its id to the line's (SentAs).
-/
theorem paired_spec {halted : Option (PeerOrigin × String)} {i j : Nat}
    (h : peerFindings service d arrivals lines peerLines halted = [])
    (hp : peerPaired? service d arrivals lines peerLines i = some j) :
    ∃ al bl, lines[i]? = some al ∧ peerLines[j]? = some bl ∧ j < peerBefore arrivals peerLines i ∧
      SentAs (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
        (peerBindings service d arrivals lines peerLines i)
        (peerBindings service d arrivals lines peerLines (i + 1)) al bl := by
  unfold peerPaired? at hp
  split at hp
  · next hc =>
    cases hal : lines[i]? with
    | none => simp [hal] at hp
    | some al =>
      simp only [hal, Option.bind_some, Option.map_eq_some_iff] at hp
      obtain ⟨⟨j', bs'⟩, hs, he⟩ := hp
      simp only at he
      subst he
      have hs' : peerSent (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
          (peerBindings service d arrivals lines peerLines i)
          (peerLines.take (peerBefore arrivals peerLines i)) al = .ok (j', bs') := by
        revert hs
        cases peerSent (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
          (peerBindings service d arrivals lines peerLines i)
          (peerLines.take (peerBefore arrivals peerLines i)) al <;> simp [Except.toOption]
      obtain ⟨bl, hbl, hS⟩ := peerSent_spec hs'
      obtain ⟨hj, hbl⟩ := getElem?_take_some hbl
      have heq := peerLine_paired hc hs' (peerLine_ok h hal)
      rw [heq]
      exact ⟨al, bl, rfl, hbl, hj, hS⟩
  · cases hp

theorem filterMap_lt {α : Type} {f : α → Option Nat} :
    ∀ {l : List α} {k k' : Nat} {a a' : α} {x y : Nat}, (l.filterMap f).Pairwise (· < ·) → l[k]? = some a →
      l[k']? = some a' → f a = some x → f a' = some y → k < k' → x < y
  | [], _, _, _, _, _, _, _, hk, _, _, _, _ => by simp at hk
  | _, _, 0, _, _, _, _, _, _, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | z :: zs, 0, k' + 1, a, a', x, y, hp, hk, hk', ha, ha', _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    simp only [List.getElem?_cons_succ] at hk'
    subst hk
    rw [List.filterMap_cons_some ha, List.pairwise_cons] at hp
    exact hp.1 y (List.mem_filterMap.mpr ⟨a', List.mem_of_getElem? hk', ha'⟩)
  | z :: zs, k + 1, k' + 1, a, a', x, y, hp, hk, hk', ha, ha', hlt => by
    have hp' : (zs.filterMap f).Pairwise (· < ·) := hp.sublist ((List.sublist_cons_self z zs).filterMap f)
    exact filterMap_lt hp' hk hk' ha ha' (by omega)

theorem peerInputs_lines_lt {k k' i i' : Nat} {x x' : Step}
    (hk : (peerInputs service d lines peerLines)[k]? = some (x, .line i))
    (hk' : (peerInputs service d lines peerLines)[k']? = some (x', .line i')) (hlt : k < k') : i < i' :=
  filterMap_lt (f := (·.2.line?)) peerInputs_lines_pairwise hk hk' rfl rfl hlt

end Tazuna.Thm.Semantics.System.PeerCheck
