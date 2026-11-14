import Tazuna.Network
import Tazuna.Thm.Semantics.System.Peer

/-!
Stage 2 of the check of a scenario's mocks of a peer (network_realizes): when the check finds no violation, the
scenario's run and the peer's run form an execution on a well formed network. The execution is built from the two runs
directly: a request reaches the peer at the time the scenario sends it, and an answer or event reaches the scenario at
the time the scenario takes it.
-/

namespace Tazuna.Thm.Network

open Tazuna.Data Tazuna.Semantics Tazuna.Network Tazuna.Thm.Semantics.System.Peer

theorem answersTo_append (xs ys : List TraceLine) (d : Dir) (to : String) :
    answersTo (xs ++ ys) d to = answersTo xs d to ++ answersTo ys d to := by
  simp [answersTo, List.filterMap_append]

theorem answersTo_take_succ {lines : List TraceLine} {i : Nat} {l : TraceLine} {d : Dir} {id : Option String}
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

theorem answersTo_take_lt {lines : List TraceLine} {i i' : Nat} {l : TraceLine} {d : Dir} {id : Option String}
    {to : String} {a : Answer} (hi : lines[i]? = some l) (hl : l.body = .answer d id to a) (h : i < i') :
    (answersTo (lines.take i) d to).length < (answersTo (lines.take i') d to).length := by
  have := answersTo_take_mono (lines := lines) (d := d) (to := to) (Nat.succ_le_of_lt h)
  rw [answersTo_take_succ hi hl, List.length_append] at this
  simp at this
  omega

theorem answersTo_at {lines : List TraceLine} {j : Nat} {l : TraceLine} {d : Dir} {id : Option String} {to : String}
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

theorem mem_inLines {lines : List TraceLine} {l : TraceLine} {j : Nat} (h : (l, j) ∈ inLines lines) :
    lines[j]? = some l ∧ l.body.dir = .in := by
  simp only [inLines, List.mem_filter, beq_iff_eq] at h
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.mp h.1, h.2⟩

theorem inLines_index {lines : List TraceLine} {k k' j : Nat} {l l' : TraceLine}
    (h : (inLines lines)[k]? = some (l, j)) (h' : (inLines lines)[k']? = some (l', j)) : k = k' := by
  have hn : ((inLines lines).map Prod.snd).Nodup := by
    refine List.Nodup.sublist (List.filter_sublist.map _) ?_
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hk : k < ((inLines lines).map Prod.snd).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp h).1
  exact (List.Nodup.getElem?_inj hk hn).mp (by simp [List.getElem?_map, h, h'])

theorem runOf_isSome {canon : String → Value → Value} {inputs : List Step} {lines : List TraceLine} {k : Nat}
    {x : Step} (h : RunOf canon inputs lines) (hx : inputs[k]? = some x) : ∃ p, (inLines lines)[k]? = some p := by
  have hk := (List.getElem?_eq_some_iff.mp hx).1
  rw [h.1] at hk
  exact ⟨_, List.getElem?_eq_getElem hk⟩

theorem mem_peerInputs_line {service peer : String} {state : List Step} {elsewhere : List (Nat × Step)}
    {aLines : List TraceLine} {st : Step} {i : Nat}
    (h : (st, Origin.line i) ∈ peerInputs service peer state elsewhere aLines) :
    ∃ l b, aLines[i]? = some l ∧ peerBody? peer aLines (peerKeys service aLines) l = some b ∧
      st = ⟨l.time, b, none, none⟩ := by
  simp only [peerInputs, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ⟨_, _, he⟩ | ⟨a, ⟨n, _, ha⟩, he⟩
  · simp at he
  · rcases ha with ⟨_, _, rfl⟩ | ha
    · simp at he
    · cases hl : aLines[n]? with
      | none => simp [hl] at ha
      | some l =>
        simp only [hl, Option.mem_toList, Option.map_eq_some_iff] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        simp only [Prod.mk.injEq, Origin.line.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨l, b, hl, hb, rfl⟩

theorem peerInputs_line_mem {service peer : String} {state : List Step} {elsewhere : List (Nat × Step)}
    {aLines : List TraceLine} {i : Nat} {l : TraceLine} {b : Step.Body} (hi : aLines[i]? = some l)
    (hb : peerBody? peer aLines (peerKeys service aLines) l = some b) :
    (⟨l.time, b, none, none⟩, Origin.line i) ∈ peerInputs service peer state elsewhere aLines := by
  simp only [peerInputs, List.mem_append, List.mem_map, List.mem_flatMap]
  refine .inr ⟨(⟨l.time, b, none, none⟩, Origin.line i), ⟨i, ?_, .inr ?_⟩, rfl⟩
  · have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.mem_range]
    omega
  · simp [hi, hb]

theorem peerBody_isSome {peer : String} {lines : List TraceLine} {keys : Bindings} {l : TraceLine} :
    (peerBody? peer lines keys l).isSome = (peerBody? peer lines [] l).isSome := by
  simp only [peerBody?]
  split <;> simp

/--
The peer's `in` line for a request or end of subscription of the scenario's run carries that line, at the same time.
-/
theorem peerBody_carries {agree : Agree} {e : Execution} {canon : String → Value → Value} {peer : String}
    {lines : List TraceLine} {keys : Bindings} {al l : TraceLine} {b : Step.Body}
    (hname : e.name 1 = peer) (hagree : ∀ n x, agree 0 1 n x (canon n (keys.rename x)))
    (hb : peerBody? peer lines keys al = some b) (hw : Writes canon ⟨al.time, b, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧ isEventLine l = false ∧
      (∀ id to a, l.body ≠ .answer .in id to a) ∧ Carries agree e 0 1 al l := by
  obtain ⟨ht, hd, hw⟩ := hw
  simp only at ht hw
  simp only [peerBody?] at hb
  split at hb
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [isEventLine, hl], by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨trivial, hn, hagree n x⟩
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [isEventLine, hl], by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨trivial, hn, hagree n x⟩
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [isEventLine, hl], by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨trivial, hn, hagree n x⟩
  next _ _ to hal =>
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb
    obtain ⟨_, rfl⟩ := hb
    obtain ⟨id', hl⟩ := hw
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [isEventLine, hl], by simp [hl], ?_⟩
    simp only [Carries, hal, hl]
  next => simp at hb

theorem peerTarget_none {p : String} {lines : List TraceLine}
    (h : ∀ l ∈ lines, ∀ n, l.body.name? = some n → peerName? p n = none) (to : String) :
    peerTarget? p lines to = none := by
  simp only [peerTarget?, List.findSome?_eq_none_iff]
  intro l hl
  split
  all_goals first
    | rfl
    | (split
       · apply h l hl
         simp_all [TraceLine.Body.name?]
       · rfl)

theorem peerBody_none {p : String} {lines : List TraceLine} {keys : Bindings} {l : TraceLine}
    (h : ∀ l ∈ lines, ∀ n, l.body.name? = some n → peerName? p n = none) (hl : l ∈ lines) :
    peerBody? p lines keys l = none := by
  simp only [peerBody?]
  split
  all_goals first
    | rfl
    | (simp [peerTarget_none h]; done)
    | (rename_i hb
       simp only [Option.map_eq_none_iff, ite_eq_left_iff, Bool.not_eq_true]
       exact fun _ => h l hl _ (by simp [hb, TraceLine.Body.name?]))

theorem sameAnswer_carries {norm seen : Value → Value} {agree : Value → Value → Prop} {a b : Answer}
    (hagree : ∀ x y, (norm y).canonical = (norm (seen x)).canonical → agree x y)
    (h : sameAnswer norm seen a b = true) : AnswerCarries agree b a := by
  cases a with
  | accepted o =>
    cases b with
    | accepted p =>
      cases o <;> cases p <;> simp_all [sameAnswer, AnswerCarries]
    | _ => simp [sameAnswer] at h
  | fulfilled o =>
    cases b with
    | fulfilled p => exact hagree _ _ (by simpa [sameAnswer] using h)
    | _ => simp [sameAnswer] at h
  | rejected r =>
    cases b with
    | rejected q =>
      simp only [sameAnswer, beq_iff_eq] at h
      exact h.symm
    | _ => simp [sameAnswer] at h

theorem unreached_of {lines : List TraceLine} {i : Nat} {l : TraceLine} {id : Option String} {to : String}
    {rejection : Rejection} (hl : lines[i]? = some l) (hb : l.body = .answer .in id to (.rejected rejection))
    (hk : rejection.kind = .unavailable) : unreached lines to = true := by
  simp only [unreached, List.any_eq_true]
  exact ⟨l, List.mem_of_getElem? hl, by simp [hb, hk]⟩

open Classical in
/--
The line of the peer's run that the scenario's line `i` received: the peer's answer at the same place for a mocked
answer to a request to the peer that reached it, and a line that emits the event for a received event of the peer.
-/
noncomputable def sourceA (normal : String → Value → Value) (service peer : String) (aLines bLines : List TraceLine)
    (i : Nat) : Option Place :=
  match aLines[i]? with
  | some l =>
    match l.body with
    | .answer .in _ to _ =>
      if (peerTarget? peer aLines to).isSome ∧ unreached aLines to = false then
        if h : ∃ j, AnswerAt bLines .out to (answersTo (aLines.take i) .in to).length j then some (1, h.choose)
        else none
      else none
    | .event .in _ name payload _ =>
      match peerName? peer name with
      | some n =>
        if h : ∃ j b, bLines[j]? = some b ∧
            emitted (normal n) (peerSeen normal service peer aLines bLines) n payload l.time b = true then
          some (1, h.choose)
        else none
      | none => none
    | _ => none
  | none => none

/-- The place in the peer's run of the `in` line of the input that the scenario's line `i` gives the peer. -/
def deliveredAt (inputs : List (Step × Origin)) (bLines : List TraceLine) (i : Nat) : Option Nat :=
  ((inputs.zip (inLines bLines)).find? (·.1.2 == Origin.line i)).map (·.2.2)

open Classical in
/-- The scenario's line that the peer's line `j` received. -/
noncomputable def sourceB (inputs : List (Step × Origin)) (bLines : List TraceLine) (j : Nat) : Option Place :=
  if h : ∃ i, deliveredAt inputs bLines i = some j then some (0, h.choose) else none

theorem sourceA_cases {normal : String → Value → Value} {service peer : String} {aLines bLines : List TraceLine}
    {i s j : Nat} (h : sourceA normal service peer aLines bLines i = some (s, j)) :
    s = 1 ∧ ∃ al, aLines[i]? = some al ∧
      ((∃ id to a, al.body = .answer .in id to a ∧ (peerTarget? peer aLines to).isSome ∧
          unreached aLines to = false ∧ AnswerAt bLines .out to (answersTo (aLines.take i) .in to).length j) ∨
        (∃ id name payload resultOf n bl, al.body = .event .in id name payload resultOf ∧
          peerName? peer name = some n ∧ bLines[j]? = some bl ∧
          emitted (normal n) (peerSeen normal service peer aLines bLines) n payload al.time bl = true)) := by
  unfold sourceA at h
  split at h
  · next al hi =>
    split at h
    · next id to a hb =>
      split at h
      · next hc =>
        split at h
        · next hex =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, al, hi, .inl ⟨id, to, a, hb, hc.1, hc.2, hex.choose_spec⟩⟩
        · simp at h
      · simp at h
    · next id name payload resultOf hb =>
      split at h
      · next n hn =>
        split at h
        · next hex =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨bl, hbl, he⟩ := hex.choose_spec
          exact ⟨rfl, al, hi, .inr ⟨id, name, payload, resultOf, n, bl, hb, hn, hbl, he⟩⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem deliveredAt_spec {inputs : List (Step × Origin)} {bLines : List TraceLine} {i j : Nat}
    (h : deliveredAt inputs bLines i = some j) :
    ∃ (k : Nat) (st : Step) (l : TraceLine),
      inputs[k]? = some (st, Origin.line i) ∧ (inLines bLines)[k]? = some (l, j) := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hx)
  rw [List.getElem?_zip_eq_some] at hk
  obtain ⟨⟨st, o⟩, l, j⟩ := x
  simp only [beq_iff_eq] at hp
  subst hp
  exact ⟨k, st, l, hk.1, hk.2⟩

theorem deliveredAt_of {inputs : List (Step × Origin)} {bLines : List TraceLine} {i k : Nat} {st : Step}
    {p : TraceLine × Nat} (hi : inputs[k]? = some (st, Origin.line i)) (hp : (inLines bLines)[k]? = some p) :
    ∃ j, deliveredAt inputs bLines i = some j := by
  unfold deliveredAt
  cases hf : (inputs.zip (inLines bLines)).find? (·.1.2 == Origin.line i) with
  | none =>
    have hm : ((st, Origin.line i), p) ∈ inputs.zip (inLines bLines) :=
      List.mem_iff_getElem?.mpr ⟨k, List.getElem?_zip_eq_some.mpr ⟨hi, hp⟩⟩
    have := List.find?_eq_none.mp hf _ hm
    simp at this
  | some x => exact ⟨x.2.2, rfl⟩

theorem deliveredAt_inj {inputs : List (Step × Origin)} {bLines : List TraceLine} {i i' j : Nat}
    (h : deliveredAt inputs bLines i = some j) (h' : deliveredAt inputs bLines i' = some j) : i = i' := by
  obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec h
  obtain ⟨k', st', l', hk', hl'⟩ := deliveredAt_spec h'
  cases inLines_index hl hl'
  rw [hk] at hk'
  simp only [Option.some.injEq, Prod.mk.injEq, Origin.line.injEq] at hk'
  exact hk'.2

theorem sourceB_spec {inputs : List (Step × Origin)} {bLines : List TraceLine} {j s i : Nat}
    (h : sourceB inputs bLines j = some (s, i)) : s = 0 ∧ deliveredAt inputs bLines i = some j := by
  unfold sourceB at h
  split at h
  · next hex =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hex.choose_spec⟩
  · simp at h

theorem sourceB_of {inputs : List (Step × Origin)} {bLines : List TraceLine} {i j : Nat}
    (h : deliveredAt inputs bLines i = some j) : sourceB inputs bLines j = some (0, i) := by
  have hex : ∃ i, deliveredAt inputs bLines i = some j := ⟨i, h⟩
  unfold sourceB
  rw [dite_eq_left hex, deliveredAt_inj hex.choose_spec h]

/--
Stage 2 of the check of a scenario's mocks of a peer. Let `aLines` be the scenario's run of the service `service`, and
`bLines` a run of the peer `peer`, whose `in` lines are those that a run writes for the derived inputs (peerInputs),
and which names no definition of `service`. When the check finds no violation, an execution of the two runs on a well
formed network exists: each request of the scenario's run to the peer that reached it arrives at the peer at its send
time, and each mocked answer and received event of the peer comes from the peer's run, sent at or before the time the
scenario receives it, with the values that the two runs see (peerAgree).
-/
theorem network_realizes {normal canon : String → Value → Value} {service peer : String} {state : List Step}
    {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {halted : Option (Origin × String)}
    (hrun : RunOf canon ((peerInputs service peer state elsewhere aLines).map (·.1)) bLines)
    (hstar : ∀ l ∈ bLines, ∀ n, l.body.name? = some n → peerName? service n = none)
    (h : peerFindings normal service peer aLines bLines halted = []) :
    ∃ source, WellFormed (peerAgree normal canon service peer aLines bLines)
      ⟨[(service, aLines), (peer, bLines)], source⟩ := by
  let inputs := peerInputs service peer state elsewhere aLines
  let keys := peerKeys service aLines
  let source : Place → Option Place
    | (0, i) => sourceA normal service peer aLines bLines i
    | (1, j) => sourceB inputs bLines j
    | _ => none
  let e : Execution := ⟨[(service, aLines), (peer, bLines)], source⟩
  have hname0 : e.name 0 = service := rfl
  have hname1 : e.name 1 = peer := rfl
  have hlines0 : e.lines 0 = aLines := rfl
  have hlines1 : e.lines 1 = bLines := rfl
  have hline0 : ∀ i, e.line? (0, i) = aLines[i]? := fun _ => rfl
  have hline1 : ∀ j, e.line? (1, j) = bLines[j]? := fun _ => rfl
  have hline2 : ∀ m j, e.line? (m + 1 + 1, j) = none := fun _ _ => by
    simp [Execution.line?, Execution.lines, e]
  have hsrc2 : ∀ m j, e.source (m + 1 + 1, j) = none := fun _ _ => rfl
  have hlen : e.members.length = 2 := rfl
  have fromB : ∀ j i, sourceB inputs bLines j = some (0, i) → ∃ al l,
      aLines[i]? = some al ∧ bLines[j]? = some l ∧ al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧
        isEventLine l = false ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
        Carries (peerAgree normal canon service peer aLines bLines) e 0 1 al l := by
    intro j i hs
    obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec (sourceB_spec hs).2
    obtain ⟨al, b, hal, hb, rfl⟩ := mem_peerInputs_line (List.mem_of_getElem? hk)
    have hw := hrun.2 k _ _ (by rw [List.getElem?_map, show inputs[k]? = _ from hk]; rfl) hl
    exact ⟨al, l, hal, (mem_inLines (List.mem_of_getElem? hl)).1,
      peerBody_carries hname1 (fun _ _ => rfl) hb hw⟩
  have fromA : ∀ i s j, sourceA normal service peer aLines bLines i = some (s, j) → ∃ al bl,
      aLines[i]? = some al ∧ bLines[j]? = some bl ∧ bl.body.dir = .out ∧ al.body.dir = .in ∧
        bl.time.time ≤ al.time.time ∧ Carries (peerAgree normal canon service peer aLines bLines) e 1 0 bl al := by
    intro i s j hs
    obtain ⟨_, al, hal, hc⟩ := sourceA_cases hs
    rcases hc with ⟨id, to, a, hb, ht, hu, bl, id', b, hbl, hbb, hk⟩ |
      ⟨id, name, payload, resultOf, n, bl, hb, hn, hbl, he⟩
    · obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp ht
      obtain ⟨t, b', hb', hsame, hle⟩ := mocked_answer_given h hal hb htarget hu
      have hat := answersTo_at hbl hbb
      rw [hk, hb'] at hat
      simp only [Option.some.injEq, Prod.mk.injEq] at hat
      obtain ⟨rfl, rfl⟩ := hat
      refine ⟨al, bl, hal, hbl, by simp [hbb, TraceLine.Body.dir], by simp [hb, TraceLine.Body.dir], hle, ?_⟩
      simp only [Carries, hbb, hb, hname1, hlines0]
      exact ⟨trivial, target, htarget, sameAnswer_carries (fun _ _ hxy => hxy) hsame⟩
    · simp only [emitted] at he
      split at he
      · next id' m p ro hbb =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
        obtain ⟨⟨rfl, hp⟩, hle⟩ := he
        refine ⟨al, bl, hal, hbl, by simp [hbb, TraceLine.Body.dir], by simp [hb, TraceLine.Body.dir], hle, ?_⟩
        simp only [Carries, hbb, hb, hname1]
        exact ⟨hn, hp.symm⟩
      · simp at he
  refine ⟨source, show WellFormed _ e from ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r i s j hs
    obtain _ | _ | r := r
    · obtain ⟨rfl, -⟩ := sourceA_cases hs
      obtain ⟨al, bl, hal, hbl, h1, h2, h3, h4⟩ := fromA i 1 j hs
      exact ⟨by decide, bl, al, hbl, hal, h1, h2, h3, h4⟩
    · obtain ⟨rfl, -⟩ := sourceB_spec hs
      obtain ⟨al, l, hal, hl, h1, h2, h3, -, -, h4⟩ := fromB i j hs
      exact ⟨by decide, al, l, hal, hl, h1, h3, by rw [h2]; exact Int.le_refl _, h4⟩
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)
  · rintro ⟨r, i⟩ ⟨r', i'⟩ ⟨s, j⟩ sent hp hq hx hev
    obtain _ | _ | r := r
    · obtain ⟨rfl, al, hal, hc⟩ := sourceA_cases hp
      have hsent : bLines[j]? = some sent := hx
      obtain _ | _ | r' := r'
      · obtain ⟨-, al', hal', hc'⟩ := sourceA_cases hq
        rcases hc with ⟨id, to, a, hb, -, -, hk⟩ | ⟨_, _, _, _, _, bl, -, -, hbl, he⟩
        · rcases hc' with ⟨id', to', a', hb', -, -, hk'⟩ | ⟨_, _, _, _, _, bl, -, -, hbl, he⟩
          · obtain ⟨rfl, hkk⟩ := answerAt_same hk hk'
            rcases Nat.lt_trichotomy i i' with hlt | rfl | hgt
            · have := answersTo_take_lt hal hb hlt
              omega
            · rfl
            · have := answersTo_take_lt hal' hb' hgt
              omega
          · rw [hsent] at hbl
            cases hbl
            simp only [emitted] at he
            split at he
            · next hbb => simp [isEventLine, hbb] at hev
            · simp at he
        · rw [hsent] at hbl
          cases hbl
          simp only [emitted] at he
          split at he
          · next hbb => simp [isEventLine, hbb] at hev
          · simp at he
      · exact absurd (sourceB_spec hq).1 (by decide)
      · exact absurd (hq.symm.trans (hsrc2 r' i')) (by simp)
    · obtain ⟨rfl, hd⟩ := sourceB_spec hp
      obtain _ | _ | r' := r'
      · exact absurd (sourceA_cases hq).1 (by decide)
      · obtain ⟨-, hd'⟩ := sourceB_spec hq
        rw [hd] at hd'
        cases hd'
        rfl
      · exact absurd (hq.symm.trans (hsrc2 r' i')) (by simp)
    · exact absurd (hp.symm.trans (hsrc2 r i)) (by simp)
  · intro r i i' s j j' l l' id id' to a a' hlt hs hs' hl hl' hb hb'
    obtain _ | _ | r := r
    · obtain ⟨-, al, hal, hc⟩ := sourceA_cases hs
      obtain ⟨-, al', hal', hc'⟩ := sourceA_cases hs'
      have hl0 : aLines[i]? = some l := hl
      have hl0' : aLines[i']? = some l' := hl'
      rw [hal] at hl0
      cases hl0
      rw [hal'] at hl0'
      cases hl0'
      rcases hc with ⟨_, _, _, hb1, -, -, hk⟩ | ⟨_, _, _, _, _, _, hb1, -⟩ <;> rw [hb] at hb1 <;> cases hb1
      rcases hc' with ⟨_, _, _, hb2, -, -, hk'⟩ | ⟨_, _, _, _, _, _, hb2, -⟩ <;> rw [hb'] at hb2 <;> cases hb2
      exact answerAt_lt hk hk' (answersTo_take_lt hal hb hlt)
    · obtain ⟨rfl, -⟩ := sourceB_spec hs
      obtain ⟨_, l1, -, hl1, -, -, -, -, hna, -⟩ := fromB _ _ hs
      have hl1' : bLines[i]? = some l := hl
      rw [hl1] at hl1'
      cases hl1'
      exact absurd hb (hna _ _ _)
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)
  · intro r i l id to rejection hl hb hk
    obtain _ | _ | r := r
    · show sourceA normal service peer aLines bLines i = none
      cases hs : sourceA normal service peer aLines bLines i with
      | none => rfl
      | some x =>
        obtain ⟨-, al, hal, hc⟩ := sourceA_cases hs
        have hl0 : aLines[i]? = some l := hl
        rw [hal] at hl0
        cases hl0
        rcases hc with ⟨_, _, _, hb1, -, hu, -⟩ | ⟨_, _, _, _, _, _, hb1, -⟩ <;> rw [hb] at hb1 <;> cases hb1
        rw [unreached_of hal hb hk] at hu
        cases hu
    · show sourceB inputs bLines i = none
      cases hs : sourceB inputs bLines i with
      | none => rfl
      | some x =>
        obtain ⟨s, j⟩ := x
        obtain ⟨rfl, -⟩ := sourceB_spec hs
        obtain ⟨_, l1, -, hl1, -, -, -, -, hna, -⟩ := fromB _ _ hs
        have hl1' : bLines[i]? = some l := hl
        rw [hl1] at hl1'
        cases hl1'
        exact absurd hb (hna _ _ _)
    · rfl
  · intro r s i l id to a hsr hslen hl hb ht hu
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : aLines[i]? = some l := hl
        have ht' : (peerTarget? peer aLines to).isSome := ht
        have hu' : unreached aLines to = false := hu
        obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp ht'
        obtain ⟨t, b, hb', -, -⟩ := mocked_answer_given h hl0 hb htarget hu'
        obtain ⟨j, bl, id', hbl, hbb, -, hk⟩ := answersTo_getElem? hb'
        have hex : ∃ j, AnswerAt bLines .out to (answersTo (aLines.take i) .in to).length j :=
          ⟨j, bl, id', b, hbl, hbb, hk⟩
        refine ⟨hex.choose, ?_⟩
        show sourceA normal service peer aLines bLines i = some (1, hex.choose)
        unfold sourceA
        simp only [hl0, hb]
        rw [ite_eq_left ⟨ht', hu'⟩, dite_eq_left hex]
      · omega
    · obtain _ | _ | s := s
      · have ht' : (peerTarget? service bLines to).isSome := ht
        rw [peerTarget_none hstar to] at ht'
        cases ht'
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)
  · intro r s i l id name n payload resultOf hsr hslen hl hb hn
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : aLines[i]? = some l := hl
        have hn' : peerName? peer name = some n := hn
        obtain ⟨bl, hbm, he⟩ := received_event_emitted h hl0 hb hn'
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbm
        have hex : ∃ j b, bLines[j]? = some b ∧
            emitted (normal n) (peerSeen normal service peer aLines bLines) n payload l.time b = true :=
          ⟨j, bl, hj, he⟩
        refine ⟨hex.choose, ?_⟩
        show sourceA normal service peer aLines bLines i = some (1, hex.choose)
        unfold sourceA
        simp only [hl0, hb, hn']
        rw [dite_eq_left hex]
      · omega
    · obtain _ | _ | s := s
      · have hl1 : bLines[i]? = some l := hl
        have hn' : peerName? service name = some n := hn
        rw [hstar l (List.mem_of_getElem? hl1) name (by simp [hb, TraceLine.Body.name?])] at hn'
        cases hn'
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)
  · intro r s i l hsr hslen hl hsend
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : aLines[i]? = some l := hl
        have hsend' : (peerBody? peer aLines [] l).isSome := hsend
        rw [← peerBody_isSome (keys := keys)] at hsend'
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsend'
        obtain ⟨k, hk⟩ :=
          List.mem_iff_getElem?.mp (peerInputs_line_mem (state := state) (elsewhere := elsewhere) hl0 hb)
        have hkm : (inputs.map (·.1))[k]? = some ⟨l.time, b, none, none⟩ := by
          rw [List.getElem?_map, show inputs[k]? = _ from hk]
          rfl
        obtain ⟨p, hp⟩ := runOf_isSome hrun hkm
        obtain ⟨j, hj⟩ := deliveredAt_of hk hp
        exact ⟨j, sourceB_of hj⟩
      · omega
    · obtain _ | _ | s := s
      · have hl1 : bLines[i]? = some l := hl
        have hsend' : (peerBody? service bLines [] l).isSome := hsend
        rw [peerBody_none hstar (List.mem_of_getElem? hl1)] at hsend'
        cases hsend'
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)

end Tazuna.Thm.Network
