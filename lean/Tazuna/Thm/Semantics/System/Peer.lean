import Tazuna.Semantics.System.Peer

namespace Tazuna.Thm.Semantics.System.Peer

open Tazuna.Data Tazuna.Semantics

variable {normal : String → Value → Value} {service peer : String} {aLines bLines : List TraceLine}

/-- No violation means that the peer's run of the derived inputs did not halt. -/
theorem peerFindings_halted {halted : Option (Origin × String)}
    (h : peerFindings normal service peer aLines bLines halted = []) : halted = none := by
  cases halted with
  | none => rfl
  | some p => simp [peerFindings] at h

theorem peerFinding_none {halted : Option (Origin × String)} {i : Nat} {l : TraceLine}
    (h : peerFindings normal service peer aLines bLines halted = []) (hi : aLines[i]? = some l) :
    peerFinding normal peer (peerSeen normal service peer aLines bLines) aLines bLines i l = none := by
  cases peerFindings_halted h
  simp only [peerFindings] at h
  have hz : (l, i) ∈ aLines.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  have := List.filterMap_eq_nil_iff.mp h _ hz
  simpa using this

/--
Stage 1 for answers: with no violation, each answer that a mock gives to a request to the peer that reached it is, as
the scenario sees the peer's values (peerSeen), the peer's answer to the request at the same place, the k-th answer to
it when the mock is the k-th, and the peer gives it at or before the mock's time.
-/
theorem mocked_answer_given {halted : Option (Origin × String)} {i : Nat} {l : TraceLine} {id : Option String}
    {to target : String} {a : Answer}
    (h : peerFindings normal service peer aLines bLines halted = []) (hi : aLines[i]? = some l)
    (hl : l.body = .answer .in id to a) (ht : peerTarget? peer aLines to = some target)
    (hu : unreached aLines to = false) :
    ∃ t b, (answersTo bLines .out to)[(answersTo (aLines.take i) .in to).length]? = some (t, b) ∧
      sameAnswer (normal target) (peerSeen normal service peer aLines bLines) a b = true ∧
        t.time ≤ l.time.time := by
  have hf := peerFinding_none h hi
  simp only [peerFinding, hl, ht, hu, Bool.false_eq_true, ↓reduceIte] at hf
  split at hf
  · simp at hf
  · next t b hb =>
    refine ⟨t, b, hb, ?_⟩
    split at hf
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc
    · simp at hf

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
peer that reached it are, in order and as the scenario sees the peer's values (peerSeen), a prefix of the peer's
answers to the request, each given at or before the mock's time.
-/
theorem mocked_answers_prefix {halted : Option (Origin × String)} {to target : String} {k : Nat} {t : DateTime}
    {a : Answer} (h : peerFindings normal service peer aLines bLines halted = [])
    (ht : peerTarget? peer aLines to = some target)
    (hu : unreached aLines to = false) (hk : (answersTo aLines .in to)[k]? = some (t, a)) :
    ∃ t' b, (answersTo bLines .out to)[k]? = some (t', b) ∧
      sameAnswer (normal target) (peerSeen normal service peer aLines bLines) a b = true ∧ t'.time ≤ t.time := by
  obtain ⟨i, l, id, hi, hl, rfl, rfl⟩ := answersTo_getElem? hk
  exact mocked_answer_given h hi hl ht hu

/--
Stage 1 for events: with no violation, the peer emits each event of the peer that the scenario receives, with the same
payload as the scenario sees the peer's values (peerSeen), at or before the time the scenario receives it. Two
deliveries of one event may name the same line of the peer.
-/
theorem received_event_emitted {halted : Option (Origin × String)} {i : Nat} {l : TraceLine} {id : Option String}
    {name n : String} {payload : Value} {resultOf : Option String}
    (h : peerFindings normal service peer aLines bLines halted = []) (hi : aLines[i]? = some l)
    (hl : l.body = .event .in id name payload resultOf) (hn : peerName? peer name = some n) :
    ∃ b ∈ bLines, emitted (normal n) (peerSeen normal service peer aLines bLines) n payload l.time b = true := by
  have hf := peerFinding_none h hi
  simp only [peerFinding, hl, hn] at hf
  split at hf
  · rename_i hc
    exact List.any_eq_true.mp hc
  · simp at hf

end Tazuna.Thm.Semantics.System.Peer
