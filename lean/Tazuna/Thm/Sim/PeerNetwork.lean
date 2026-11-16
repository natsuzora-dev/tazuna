import Tazuna.Sim.PeerNetwork
import Tazuna.Thm.Sim.PeerCheck

/-!
Stage 2 of the check of a scenario's mocks of a peer (network_realizes): when the check finds no violation, the
scenario's run and the peer's run form an execution on a well formed network. The execution is built from the two runs
directly: a request or an answer reaches the peer at the time the scenario sends it, and an answer, event or request
reaches the scenario at the time the scenario takes it.
-/

namespace Tazuna.Thm.Sim.PeerNetwork

open Tazuna.Data Tazuna.Semantics Tazuna.Semantics.Network Tazuna.Thm.Data.Trace Tazuna.Thm.Data.Unify
  Tazuna.Thm.Sim.Peer Tazuna.Thm.Sim.PeerCheck Tazuna.Thm.Verify.Matching

theorem runOf_isSome {canon : Schema → Value → Value} {inputs : List Step} {lines : List TraceLine} {k : Nat}
    {x : Step} (h : RunOf canon inputs lines) (hx : inputs[k]? = some x) : ∃ p, (inLines lines)[k]? = some p := by
  have hk := (List.getElem?_eq_some_iff.mp hx).1
  rw [h.1] at hk
  exact ⟨_, List.getElem?_eq_getElem hk⟩

/--
The peer's `in` line for a request or end of subscription of the scenario's run carries that line, at the same time.
-/
theorem peerBody_carries {agree : Agree} {ids : Ids} {e : Execution} {canon : Schema → Value → Value} {peer : String}
    {lines peerLines : List TraceLine} {keys : Bindings} {i : Nat} {al l : TraceLine} {b : Step.Body}
    (hname : e.name 1 = peer) (hagree : ∀ sch x, agree (0, i) 1 sch x (canon sch (keys.rename x)))
    (hids : ∀ x, ids (0, i) 1 x x)
    (hb : peerBody? peer lines keys al = some b) (hw : Writes canon peerLines ⟨al.time, b, none, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      Carries agree ids e (0, i) 1 al l := by
  obtain ⟨ht, hd, hw⟩ := hw
  simp only at ht hw
  simp only [peerBody?] at hb
  split at hb
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨hids id, hn, hagree (.input n) x⟩
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨hids id, hn, hagree (.input n) x⟩
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨hids id, hn, hagree (.input n) x⟩
  next _ _ to hal =>
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb
    obtain ⟨_, rfl⟩ := hb
    obtain ⟨id', hl⟩ := hw
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl]
    exact hids to
  next => simp at hb

/-- The peer's `in` line for an event of the scenario's run carries that line, at the same time. -/
theorem peerEvent_carries {agree : Agree} {ids : Ids} {e : Execution} {canon : Schema → Value → Value}
    {service : String} {received : List String} {peerLines : List TraceLine} {keys : Bindings} {i : Nat}
    {al l : TraceLine} {b : Step.Body}
    (hname : e.name 0 = service) (hagree : ∀ sch x, agree (0, i) 1 sch x (canon sch (keys.rename x)))
    (hb : peerEvent? service received keys al = some b) (hw : Writes canon peerLines ⟨al.time, b, none, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      Carries agree ids e (0, i) 1 al l := by
  obtain ⟨ht, hd, hw⟩ := hw
  simp only at ht hw
  simp only [peerEvent?] at hb
  split at hb
  next id name x r hal =>
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hn := List.find?_some hm
    simp only [beq_iff_eq] at hn
    obtain ⟨id', r', hl, -, -⟩ := hw
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨hn, hagree (.payload m) x⟩
  next => simp at hb

theorem AnswerCarries.mapOutput {P : Value → Value → Prop} {f : Value → Value} (h : ∀ x, P x (f x)) :
    ∀ a : Answer, AnswerCarries P a (a.mapOutput f)
  | .accepted (some x) => h x
  | .accepted none => trivial
  | .fulfilled x => h x
  | .rejected _ => rfl

/-- The peer's `in` line for an answer to its request of a from line carries the scenario's answer, at the same time. -/
theorem peerAnswer_carries {agree : Agree} {ids : Ids} {e : Execution} {canon : Schema → Value → Value}
    {service : String} {lines peerLines : List TraceLine} {fromLines : List Nat} {keys : Bindings} {i : Nat}
    {al l : TraceLine} {b : Step.Body}
    (hname : e.name 0 = service) (hlines : e.lines 1 = peerLines)
    (hagree : ∀ sch x, agree (0, i) 1 sch x (canon sch (keys.rename x)))
    (hids : ∀ x, ids (0, i) 1 x ((keys.lookup x).getD x))
    (hb : peerAnswer? service lines fromLines keys al = some b) (hw : Writes canon peerLines ⟨al.time, b, none, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧
      (∀ id to a, l.body = .answer .in id to a → a.unavailable = false) ∧ Carries agree ids e (0, i) 1 al l := by
  obtain ⟨ht, hd, hw⟩ := hw
  simp only at ht hw
  simp only [peerAnswer?] at hb
  split at hb
  next id to a hal =>
    split at hb
    · cases hb
    · next hu =>
      obtain ⟨name, -, rfl⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨id', hl, hr⟩ := hw
      refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, fun _ _ a' he => ?_, ?_⟩
      · rw [hl] at he
        cases he
        rw [unavailable_mapOutput, unavailable_mapOutput]
        simpa using hu
      · simp only [Carries, hal, hl, hname, hlines]
        refine ⟨hids to, _, hr, by rw [peerName_traceName]; rfl, ?_⟩
        rw [mapOutput_mapOutput]
        exact AnswerCarries.mapOutput (fun x => hagree _ x) a
  next => simp at hb

theorem peerInput_carries {agree : Agree} {ids : Ids} {e : Execution} {canon : Schema → Value → Value}
    {service peer : String} {received : List String} {fromLines : List Nat} {lines peerLines : List TraceLine}
    {keys : Bindings} {i : Nat} {al l : TraceLine} {b : Step.Body}
    (hname0 : e.name 0 = service) (hname1 : e.name 1 = peer) (hlines : e.lines 1 = peerLines)
    (hagree : ∀ sch x, agree (0, i) 1 sch x (canon sch (keys.rename x)))
    (hids : ∀ x, ids (0, i) 1 x x ∧ ids (0, i) 1 x ((keys.lookup x).getD x))
    (hb : peerInput? service peer received fromLines lines keys al = some b)
    (hw : Writes canon peerLines ⟨al.time, b, none, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧
      (∀ id to a, l.body = .answer .in id to a → a.unavailable = false) ∧ Carries agree ids e (0, i) 1 al l := by
  have notAnswer : ∀ {P : Prop}, (al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧
      (∀ id to a, l.body ≠ .answer .in id to a) ∧ P) → al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧
      (∀ id to a, l.body = .answer .in id to a → a.unavailable = false) ∧ P :=
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, fun id to a he => absurd he (h4 id to a), h5⟩
  simp only [peerInput?] at hb
  cases hp : peerBody? peer lines keys al with
  | some b' =>
    simp only [hp, Option.orElse_some, Option.some.injEq] at hb
    subst hb
    exact notAnswer (peerBody_carries hname1 hagree (fun x => (hids x).1) hp hw)
  | none =>
    simp only [hp, Option.orElse_none] at hb
    cases he : peerEvent? service received keys al with
    | some b' =>
      simp only [he, Option.orElse_some, Option.some.injEq] at hb
      subst hb
      exact notAnswer (peerEvent_carries hname0 hagree he hw)
    | none =>
      simp only [he, Option.orElse_none] at hb
      exact peerAnswer_carries hname0 hlines hagree (fun x => (hids x).2) hb hw

/--
The input that a run writes an `in` event line or answer line for gives a message of the definition that the line names:
the event, or the target of the answered request.
-/
theorem writes_received {canon : Schema → Value → Value} {lines : List TraceLine} {st : Step} {l : TraceLine}
    (hw : Writes canon lines st l) :
    (∀ id name payload resultOf, l.body = .event .in id name payload resultOf → st.body.received? = some name) ∧
      (∀ id to a, l.body = .answer .in id to a →
        ∃ target, st.body.received? = some target ∧ requestName? lines to = some target) := by
  obtain ⟨-, -, hw⟩ := hw
  cases hs : st.body with
  | event sid n x r =>
    simp only [hs] at hw
    obtain ⟨_, _, hl, -⟩ := hw
    refine ⟨fun _ _ _ _ hb => ?_, fun _ _ _ hb => ?_⟩ <;> rw [hb] at hl <;> cases hl
    rfl
  | answer sender target a c h =>
    simp only [hs] at hw
    obtain ⟨_, to, _, hl, hr⟩ := hw
    refine ⟨fun _ _ _ _ hb => ?_, fun _ _ _ hb => ?_⟩ <;> rw [hb] at hl <;> cases hl
    exact ⟨target, rfl, hr⟩
  | answerById to target a =>
    simp only [hs] at hw
    obtain ⟨_, hl, hr⟩ := hw
    refine ⟨fun _ _ _ _ hb => ?_, fun _ _ _ hb => ?_⟩ <;> rw [hb] at hl <;> cases hl
    exact ⟨target, rfl, hr⟩
  | command | query | subscribe =>
    simp only [hs] at hw
    obtain ⟨_, hl, -⟩ := hw
    refine ⟨fun _ _ _ _ hb => ?_, fun _ _ _ hb => ?_⟩ <;> rw [hb] at hl <;> cases hl
  | unsubscribe e =>
    cases e with
    | id to =>
      simp only [hs] at hw
      obtain ⟨_, hl⟩ := hw
      refine ⟨fun _ _ _ _ hb => ?_, fun _ _ _ hb => ?_⟩ <;> rw [hb] at hl <;> cases hl
    | handle => simp only [hs] at hw
  | _ =>
    simp only [hs] at hw
    refine ⟨fun _ _ _ _ hb => ?_, fun _ _ _ hb => ?_⟩ <;> simp [isEventLine, TraceLine.Body.to?, hb] at hw

theorem AnswerCarries.mono {P Q : Value → Value → Prop} (h : ∀ x y, P x y → Q x y) :
    ∀ {b a : Answer}, AnswerCarries P b a → AnswerCarries Q b a
  | .accepted (some _), .accepted (some _), hp => h _ _ hp
  | .accepted none, .accepted none, _ => trivial
  | .fulfilled _, .fulfilled _, hp => h _ _ hp
  | .rejected _, .rejected _, hp => hp

variable {service : String} {d : PeerDerivation} {arrivals : List Nat}
  {lines peerLines : List TraceLine}

open Classical in
/--
The line of the peer's run that the scenario's line `i` received: the peer's answer at the same place for a mocked
answer to a request to the peer that reached it, a line that emits the event for a received event of the peer, before
the peer takes an input that arrives after the line (peerBefore), and the line that sends a from line (peerPaired?).
-/
noncomputable def sourceA (service : String) (d : PeerDerivation)
    (arrivals : List Nat) (lines peerLines : List TraceLine) (i : Nat) : Option Place :=
  match lines[i]? with
  | some l =>
    match l.body with
    | .answer .in _ to _ =>
      if (peerTarget? d.peer lines to).isSome ∧ unreached lines to = false then
        if h : ∃ j, j < peerBefore arrivals peerLines i ∧ AnswerAt peerLines .out to (answersTo (lines.take i) .in to).length j
        then some (1, h.choose)
        else none
      else none
    | .event .in _ name payload resultOf =>
      match peerName? d.peer name with
      | some n =>
        if h : ∃ j b, peerLines[j]? = some b ∧ j < peerBefore arrivals peerLines i ∧ PeerEmits d.peerForm service lines peerLines
            (peerFinal service d arrivals lines peerLines) n payload resultOf l.time b then
          some (1, h.choose)
        else none
      | none => none
    | _ => (peerPaired? service d arrivals lines peerLines i).map (1, ·)
  | none => none

theorem sourceA_cases {i s j : Nat}
    (h : sourceA service d arrivals lines peerLines i = some (s, j)) :
    s = 1 ∧ ∃ al, lines[i]? = some al ∧
      ((∃ id to a, al.body = .answer .in id to a ∧ (peerTarget? d.peer lines to).isSome ∧
          unreached lines to = false ∧ AnswerAt peerLines .out to (answersTo (lines.take i) .in to).length j ∧
          j < peerBefore arrivals peerLines i) ∨
        (∃ id name payload resultOf n bl, al.body = .event .in id name payload resultOf ∧
          peerName? d.peer name = some n ∧ peerLines[j]? = some bl ∧ j < peerBefore arrivals peerLines i ∧
          PeerEmits d.peerForm service lines peerLines (peerFinal service d arrivals lines peerLines)
            n payload resultOf al.time bl) ∨
        peerPaired? service d arrivals lines peerLines i = some j) := by
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
          exact ⟨rfl, al, hi, .inl ⟨id, to, a, hb, hc.1, hc.2, hex.choose_spec.2, hex.choose_spec.1⟩⟩
        · simp at h
      · simp at h
    · next id name payload resultOf hb =>
      split at h
      · next n hn =>
        split at h
        · next hex =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨bl, hbl, hj, he⟩ := hex.choose_spec
          exact ⟨rfl, al, hi, .inr (.inl ⟨id, name, payload, resultOf, n, bl, hb, hn, hbl, hj, he⟩)⟩
        · simp at h
      · simp at h
    · obtain ⟨j', hp, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, al, hi, .inr (.inr hp)⟩
  · simp at h

/-- The place in the peer's run of the `in` line of the input that the scenario's line `i` gives the peer. -/
def deliveredAt (inputs : List (Step × PeerOrigin)) (peerLines : List TraceLine) (i : Nat) : Option Nat :=
  ((inputs.zip (inLines peerLines)).find? (·.1.2 == PeerOrigin.line i)).map (·.2.2)

open Classical in
/-- The scenario's line that the peer's line `j` received. -/
noncomputable def sourceB (inputs : List (Step × PeerOrigin)) (peerLines : List TraceLine) (j : Nat) : Option Place :=
  if h : ∃ i, deliveredAt inputs peerLines i = some j then some (0, h.choose) else none

theorem deliveredAt_spec {inputs : List (Step × PeerOrigin)} {peerLines : List TraceLine} {i j : Nat}
    (h : deliveredAt inputs peerLines i = some j) :
    ∃ (k : Nat) (st : Step) (l : TraceLine),
      inputs[k]? = some (st, PeerOrigin.line i) ∧ (inLines peerLines)[k]? = some (l, j) := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hx)
  rw [List.getElem?_zip_eq_some] at hk
  obtain ⟨⟨st, o⟩, l, j⟩ := x
  simp only [beq_iff_eq] at hp
  subst hp
  exact ⟨k, st, l, hk.1, hk.2⟩

theorem deliveredAt_of {inputs : List (Step × PeerOrigin)} {peerLines : List TraceLine} {i k : Nat} {st : Step}
    {p : TraceLine × Nat} (hi : inputs[k]? = some (st, PeerOrigin.line i)) (hp : (inLines peerLines)[k]? = some p) :
    ∃ j, deliveredAt inputs peerLines i = some j := by
  unfold deliveredAt
  cases hf : (inputs.zip (inLines peerLines)).find? (·.1.2 == PeerOrigin.line i) with
  | none =>
    have hm : ((st, PeerOrigin.line i), p) ∈ inputs.zip (inLines peerLines) :=
      List.mem_iff_getElem?.mpr ⟨k, List.getElem?_zip_eq_some.mpr ⟨hi, hp⟩⟩
    have := List.find?_eq_none.mp hf _ hm
    simp at this
  | some x => exact ⟨x.2.2, rfl⟩

theorem deliveredAt_inj {inputs : List (Step × PeerOrigin)} {peerLines : List TraceLine} {i i' j : Nat}
    (h : deliveredAt inputs peerLines i = some j) (h' : deliveredAt inputs peerLines i' = some j) : i = i' := by
  obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec h
  obtain ⟨k', st', l', hk', hl'⟩ := deliveredAt_spec h'
  cases inLines_index hl hl'
  rw [hk] at hk'
  simp only [Option.some.injEq, Prod.mk.injEq, PeerOrigin.line.injEq] at hk'
  exact hk'.2

theorem sourceB_spec {inputs : List (Step × PeerOrigin)} {peerLines : List TraceLine} {j s i : Nat}
    (h : sourceB inputs peerLines j = some (s, i)) : s = 0 ∧ deliveredAt inputs peerLines i = some j := by
  unfold sourceB at h
  split at h
  · next hex =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hex.choose_spec⟩
  · simp at h

theorem sourceB_of {inputs : List (Step × PeerOrigin)} {peerLines : List TraceLine} {i j : Nat}
    (h : deliveredAt inputs peerLines i = some j) : sourceB inputs peerLines j = some (0, i) := by
  have hex : ∃ i, deliveredAt inputs peerLines i = some j := ⟨i, h⟩
  unfold sourceB
  rw [dite_eq_left hex, deliveredAt_inj hex.choose_spec h]


/--
How the scenario's service `service`, member 0, and its peer `peer`, member 1, see each other's values. The peer
receives a value of a request, event or answer of the scenario's line `i` in the form `canon` that its run writes, with
the strings that the peer takes in place of the scenario's before that line (peerForward); the scenario's service
receives an input of a request whose ownInputForm stands for the peer's, and a value of an answer or event that stands
for the peer's (PeerSees), under the final bindings.
-/
def peerAgree (canon : Schema → Value → Value) (service : String) (d : PeerDerivation) (arrivals : List Nat)
    (lines peerLines : List TraceLine) : Agree
  | (0, i), 1, sch, x, y => y = canon sch ((peerForward service d arrivals lines peerLines i).rename x)
  | (1, _), 0, .input m, x, y =>
    ValueMatches (standsFor (createdOf peerLines) (peerFinal service d arrivals lines peerLines))
      (seenInputOf d.ownInputForm service lines m x) (d.ownInputForm m y)
  | (1, _), 0, .output m, x, y | (1, _), 0, .payload m, x, y => ∃ n, peerName? d.peer m = some n ∧
    PeerSees d.peerForm service lines peerLines (peerFinal service d arrivals lines peerLines) n x y
  | _, _, _, _, _ => False

/--
How the two members name each other's requests: the peer names a request of the scenario's line `n`, or the request of
an answer, by the same id or the one that the strings of the line take (peerForward), and the scenario's service names
a request of the peer by the same id or the one that the final bindings bind it to.
-/
def peerIds (service : String) (d : PeerDerivation) (arrivals : List Nat)
    (lines peerLines : List TraceLine) : Ids
  | (0, n), 1, i, j => j = i ∨ (peerForward service d arrivals lines peerLines n).lookup i = some j
  | (1, _), 0, i, j => j = i ∨ (peerFinal service d arrivals lines peerLines).lookup i = some j
  | _, _, _, _ => False

/--
Stage 2 of the check of a scenario's mocks of a peer. Let `lines` be the scenario's run of the service `service`, and
`peerLines` a run of the peer `d.peer` whose `in` lines are those that a run writes for the derived inputs (peerInputs), and
whose every request and end of a subscription to `service` is one that a from line takes (peerPaired?).
Nothing checks this, and a peer's run can send `service` requests that no from line takes; the check neither delivers
them nor compares them. The given state and the elsewhere inputs give the peer no event of `service` and no answer to
a request to it. When the check finds no violation, an execution of the two runs on a well formed network exists: each
request of the scenario's run to the peer that reached it, and each answer to a request of a from line, arrives at the
peer at its send time; each event of `service` that the peer receives comes from the scenario's run at its emit time;
and each mocked answer, received event of the peer, and request of a from line comes from the peer's run, sent at or
before the time the scenario takes it and before the peer receives a line that the scenario sends after it
(WellFormed.causal), with the values and ids that the two runs see (peerAgree, peerIds).
-/
theorem network_realizes {canon : Schema → Value → Value} {halted : Option (PeerOrigin × String)}
    (hrun : RunOf canon ((peerInputs service d lines peerLines).map
      (·.1)) peerLines)
    (hsent : ∀ j l, peerLines[j]? = some l → Sends service peerLines l →
      ∃ i, peerPaired? service d (peerArrivals service d lines) lines peerLines i = some j)
    (hown : ∀ s ∈ d.state ++ d.elsewhere.map (·.2), ∀ n, s.body.received? = some n → peerName? service n = none)
    (h : peerFindings service d (peerArrivals service d lines) lines peerLines halted = []) :
    ∃ source, WellFormed
      (peerAgree canon service d (peerArrivals service d lines) lines peerLines)
      (peerIds service d (peerArrivals service d lines) lines peerLines)
      ⟨[(service, lines), (d.peer, peerLines)], source⟩ := by
  let arrivals := peerArrivals service d lines
  let inputs := peerInputs service d lines peerLines
  let agree := peerAgree canon service d arrivals lines peerLines
  let ids := peerIds service d arrivals lines peerLines
  let final := peerFinal service d arrivals lines peerLines
  let source : Place → Option Place
    | (0, i) => sourceA service d arrivals lines peerLines i
    | (1, j) => sourceB inputs peerLines j
    | _ => none
  let e : Execution := ⟨[(service, lines), (d.peer, peerLines)], source⟩
  have hname0 : e.name 0 = service := rfl
  have hname1 : e.name 1 = d.peer := rfl
  have hlines1 : e.lines 1 = peerLines := rfl
  have hline2 : ∀ m j, e.line? (m + 1 + 1, j) = none := fun _ _ => by
    simp [Execution.line?, Execution.lines, e]
  have hsrc2 : ∀ m j, e.source (m + 1 + 1, j) = none := fun _ _ => rfl
  have hmembers : e.members.length = 2 := rfl
  have toFinal : ∀ {i : Nat} {l : TraceLine}, lines[i]? = some l →
      peerBindings service d arrivals lines peerLines (i + 1) <+: final :=
    fun hi => final_of hi
  have notFrom : ∀ {i j : Nat}, peerPaired? service d arrivals lines peerLines i = some j →
      ∃ al bl, lines[i]? = some al ∧ peerLines[j]? = some bl ∧ j < peerBefore arrivals peerLines i ∧
        SentAs (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
          (peerBindings service d arrivals lines peerLines i)
          (peerBindings service d arrivals lines peerLines (i + 1)) al bl :=
    fun hp => paired_spec h hp
  have fromB : ∀ j i, sourceB inputs peerLines j = some (0, i) → ∃ al l,
      lines[i]? = some al ∧ peerLines[j]? = some l ∧ al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧
        (∀ id to a, l.body = .answer .in id to a → a.unavailable = false) ∧ Carries agree ids e (0, i) 1 al l := by
    intro j i hs
    obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec (sourceB_spec hs).2
    obtain ⟨al, b, hal, hb, rfl⟩ := mem_peerInputs_line (List.mem_of_getElem? hk)
    have hw := hrun.2 k _ _ (by rw [List.getElem?_map, show inputs[k]? = _ from hk]; rfl) hl
    refine ⟨al, l, hal, (mem_inLines (List.mem_of_getElem? hl)).1,
      peerInput_carries hname0 hname1 hlines1 (fun _ _ => rfl) (fun x => ⟨.inl rfl, ?_⟩) hb hw⟩
    cases hx : (peerForward service d arrivals lines peerLines i).lookup x with
    | none => exact .inl rfl
    | some y => exact .inr (by rw [hx]; rfl)
  have fromA : ∀ i s j, sourceA service d arrivals lines peerLines i = some (s, j) →
      ∃ al bl, lines[i]? = some al ∧ peerLines[j]? = some bl ∧ bl.body.dir = .out ∧ al.body.dir = .in ∧
        bl.time.time ≤ al.time.time ∧ Carries agree ids e (1, j) 0 bl al := by
    intro i s j hs
    obtain ⟨_, al, hal, hc⟩ := sourceA_cases hs
    rcases hc with ⟨id, to, a, hb, ht, hu, ⟨bl, id', b, hbl, hbb, hk⟩, -⟩ |
      ⟨id, name, payload, resultOf, n, bl, hb, hn, hbl, -, he⟩ | hp
    · obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp ht
      obtain ⟨t, b', hb', hsame, hle⟩ := mocked_answer_given h hal hb htarget hu
      have hat := answersTo_at hbl hbb
      rw [hk, answersTo_take_getElem? hb'] at hat
      simp only [Option.some.injEq, Prod.mk.injEq] at hat
      obtain ⟨rfl, rfl⟩ := hat
      refine ⟨al, bl, hal, hbl, by simp [hbb, TraceLine.Body.dir], by simp [hb, TraceLine.Body.dir], hle, ?_⟩
      obtain ⟨m, hm, hmt⟩ := Option.bind_eq_some_iff.mp htarget
      simp only [Carries, hbb, hb, hname1]
      exact ⟨.inl rfl, m, hm, by simp [hmt], AnswerCarries.mono (fun _ _ hp => ⟨target, hmt, hp⟩) hsame⟩
    · obtain ⟨id', p, ro, hbb, hr, hle, hp⟩ := he
      refine ⟨al, bl, hal, hbl, by simp [hbb, TraceLine.Body.dir], by simp [hb, TraceLine.Body.dir], hle, ?_⟩
      simp only [Carries, hbb, hb, hname1]
      exact ⟨hn, n, hn, hp⟩
    · obtain ⟨al', bl, hal', hbl, -, hS⟩ := notFrom hp
      rw [hal] at hal'
      cases hal'
      obtain ⟨hdin, -, -, hdout, -, -⟩ := hS.request
      refine ⟨al, bl, hal, hbl, hdout, hdin, hS.time, ?_⟩
      have hbound : final.lookup bl.body.id = some al.body.id := lookup_prefix (toFinal hal) hS.bound
      rcases hS.body with ⟨t, aid, name, x, bid, m, y, hx, hy, hm, hsound⟩ | ⟨aid, to, bid, to', hl, hb, hto⟩
      · have hval := hsound final (toFinal hal)
        rw [requestOf_id hx, requestOf_id hy] at hbound
        rcases requestOf_some hx with ⟨hl, rfl⟩ | ⟨hl, rfl⟩ | ⟨hl, rfl⟩ <;>
        rcases requestOf_some hy with ⟨hb, ht⟩ | ⟨hb, ht⟩ | ⟨hb, ht⟩ <;>
        first
          | (simp at ht; done)
          | (simp only [Carries, hb, hl, hname0]
             exact ⟨.inr hbound, hm, hval⟩)
      · simp only [Carries, hb, hl]
        exact .inr (lookup_prefix (hS.grows.trans (toFinal hal)) hto)
  have hlen : arrivals.length = (inLines peerLines).length := by
    show (peerArrivals service d lines).length = _
    rw [← peerInputs_arrivals (d := d) (peerLines := peerLines), List.length_map,
      ← hrun.1, List.length_map]
  have inOf : ∀ i s j, sourceA service d arrivals lines peerLines i = some (s, j) →
      ∃ al, lines[i]? = some al ∧ al.body.dir = .in := by
    intro i s j hs
    obtain ⟨al, -, hal, -, -, hin, -⟩ := fromA i s j hs
    exact ⟨al, hal, hin⟩
  have beforeOf : ∀ i s j, sourceA service d arrivals lines peerLines i = some (s, j) →
      j < peerBefore arrivals peerLines i := by
    intro i s j hs
    obtain ⟨_, al, hal, hc⟩ := sourceA_cases hs
    rcases hc with ⟨_, _, _, _, _, _, _, hj⟩ | ⟨_, _, _, _, _, _, _, _, _, hj, _⟩ | hp
    · exact hj
    · exact hj
    · obtain ⟨_, _, _, _, hj, _⟩ := notFrom hp
      exact hj
  have notAnswerFrom : ∀ {i j : Nat} {al : TraceLine}, lines[i]? = some al →
      peerPaired? service d arrivals lines peerLines i = some j →
      (∀ id to a, al.body ≠ .answer .in id to a) ∧ ∀ bl, peerLines[j]? = some bl →
        isEventLine bl = false ∧ ∀ id to a, bl.body ≠ .answer .out id to a := by
    intro i j al hal hp
    obtain ⟨al', bl, hal', hbl, -, hS⟩ := notFrom hp
    rw [hal] at hal'
    cases hal'
    obtain ⟨-, ha, -, -, hev, hna⟩ := hS.request
    exact ⟨ha, fun bl' hbl' => by rw [hbl] at hbl'; cases hbl'; exact ⟨hev, hna⟩⟩
  have sourceOfIn : ∀ {i : Nat} {l : TraceLine}, peerLines[i]? = some l → l.body.dir = .in →
      (∀ st, Writes canon peerLines st l → ∃ n, st.body.received? = some n ∧ (peerName? service n).isSome) →
      ∃ j, sourceB inputs peerLines i = some (0, j) := by
    intro i l hl hd hrecv
    obtain ⟨k, hk⟩ := inLines_of hl hd
    obtain ⟨⟨st, o⟩, hi⟩ : ∃ x, inputs[k]? = some x := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rw [← hrun.1, List.length_map] at this
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have hw := hrun.2 k st _ (by rw [List.getElem?_map, hi]; rfl) hk
    obtain ⟨n, hr, hn⟩ := hrecv st hw
    cases o with
    | given =>
      have := hown st (List.mem_append_left _ (mem_peerInputs_given (List.mem_of_getElem? hi))) n hr
      simp [this] at hn
    | elsewhere j =>
      obtain ⟨s', hs', keys, hb'⟩ := mem_peerInputs_elsewhere (List.mem_of_getElem? hi)
      rw [hb', forPeer_received] at hr
      have := hown s' (List.mem_append_right _ hs') n hr
      simp [this] at hn
    | line i' =>
      obtain ⟨j, hj⟩ := deliveredAt_of hi hk
      obtain ⟨k', _, _, hk1, hk2⟩ := deliveredAt_spec hj
      cases peerInputs_line_unique hi hk1
      rw [hk] at hk2
      cases hk2
      exact ⟨i', sourceB_of hj⟩
  refine ⟨source, show WellFormed agree ids e from ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r i s j hs
    obtain _ | _ | r := r
    · obtain ⟨rfl, -⟩ := sourceA_cases hs
      obtain ⟨al, bl, hal, hbl, h1, h2, h3, h4⟩ := fromA i 1 j hs
      exact ⟨by decide, bl, al, hbl, hal, h1, h2, h3, h4⟩
    · obtain ⟨rfl, -⟩ := sourceB_spec hs
      obtain ⟨al, l, hal, hl, h1, h2, h3, -, h4⟩ := fromB i j hs
      exact ⟨by decide, al, l, hal, hl, h1, h3, by rw [h2]; exact Int.le_refl _, h4⟩
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)
  · rintro ⟨r, i⟩ ⟨r', i'⟩ ⟨s, j⟩ sent hp hq hx hev
    obtain _ | _ | r := r
    · obtain ⟨rfl, al, hal, hc⟩ := sourceA_cases hp
      have hsent : peerLines[j]? = some sent := hx
      obtain _ | _ | r' := r'
      · obtain ⟨-, al', hal', hc'⟩ := sourceA_cases hq
        rcases hc with ⟨id, to, a, hb, -, -, hk, -⟩ | ⟨_, _, _, _, _, bl, -, -, hbl, -, he⟩ | hpf
        · rcases hc' with ⟨id', to', a', hb', -, -, hk', -⟩ | ⟨_, _, _, _, _, bl, -, -, hbl, -, he⟩ | hpf'
          · obtain ⟨rfl, hkk⟩ := answerAt_same hk hk'
            rcases Nat.lt_trichotomy i i' with hlt | rfl | hgt
            · have := answersTo_take_lt hal hb hlt
              omega
            · rfl
            · have := answersTo_take_lt hal' hb' hgt
              omega
          · rw [hsent] at hbl
            cases hbl
            obtain ⟨_, _, _, hbb, -⟩ := he
            simp [isEventLine, hbb] at hev
          · obtain ⟨_, hna⟩ := notAnswerFrom hal' hpf'
            obtain ⟨_, _, _, hj, hjb, -⟩ := hk
            rw [hsent] at hj
            cases hj
            exact absurd hjb ((hna _ hsent).2 _ _ _)
        · rw [hsent] at hbl
          cases hbl
          obtain ⟨_, _, _, hbb, -⟩ := he
          simp [isEventLine, hbb] at hev
        · rcases hc' with ⟨id', to', a', hb', -, -, hk', -⟩ | ⟨_, _, _, _, _, bl, -, -, hbl, -, he⟩ | hpf'
          · obtain ⟨_, hna⟩ := notAnswerFrom hal hpf
            obtain ⟨_, _, _, hj, hjb, -⟩ := hk'
            rw [hsent] at hj
            cases hj
            exact absurd hjb ((hna _ hsent).2 _ _ _)
          · rw [hsent] at hbl
            cases hbl
            obtain ⟨_, _, _, hbb, -⟩ := he
            simp [isEventLine, hbb] at hev
          · obtain ⟨al1, bl1, hal1, hbl1, -, hS1⟩ := notFrom hpf
            obtain ⟨al2, bl2, hal2, hbl2, -, hS2⟩ := notFrom hpf'
            rw [hsent] at hbl1 hbl2
            cases hbl1
            cases hbl2
            have stale : ∀ {i i' : Nat} {al al' : TraceLine}, i < i' →
                SentAs (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
                  (peerBindings service d arrivals lines peerLines i)
                  (peerBindings service d arrivals lines peerLines (i + 1)) al sent →
                SentAs (createdOf peerLines) (seenInputOf d.ownInputForm service lines) d.ownInputForm service
                  (peerBindings service d arrivals lines peerLines i')
                  (peerBindings service d arrivals lines peerLines (i' + 1)) al' sent →
                False := fun hlt hA hB => by
              have := lookup_prefix (peerBindings_prefix (Nat.succ_le_of_lt hlt)) hA.bound
              rw [hB.fresh] at this
              cases this
            rcases Nat.lt_trichotomy i i' with hlt | rfl | hgt
            · exact (stale hlt hS1 hS2).elim
            · rfl
            · exact (stale hgt hS2 hS1).elim
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
      have hl0 : lines[i]? = some l := hl
      have hl0' : lines[i']? = some l' := hl'
      rw [hal] at hl0
      cases hl0
      rw [hal'] at hl0'
      cases hl0'
      rcases hc with ⟨_, _, _, hb1, -, -, hk, -⟩ | ⟨_, _, _, _, _, _, hb1, -⟩ | hpf
      · rcases hc' with ⟨_, _, _, hb2, -, -, hk', -⟩ | ⟨_, _, _, _, _, _, hb2, -⟩ | hpf'
        · rw [hb] at hb1
          cases hb1
          rw [hb'] at hb2
          cases hb2
          exact answerAt_lt hk hk' (answersTo_take_lt hal hb hlt)
        · rw [hb'] at hb2
          cases hb2
        · exact absurd hb' ((notAnswerFrom hal' hpf').1 _ _ _)
      · rw [hb] at hb1
        cases hb1
      · exact absurd hb ((notAnswerFrom hal hpf).1 _ _ _)
    · obtain ⟨rfl, hd⟩ := sourceB_spec hs
      obtain ⟨-, hd'⟩ := sourceB_spec hs'
      obtain ⟨k, st, l1, hk, hl1⟩ := deliveredAt_spec hd
      obtain ⟨k', st', l2, hk', hl2⟩ := deliveredAt_spec hd'
      refine peerInputs_lines_lt hk hk' (Nat.lt_of_not_le fun hle => ?_)
      have := inLines_le hl2 hl1 hle
      omega
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)
  · intro r i l id to rejection hl hb hk
    obtain _ | _ | r := r
    · show sourceA service d arrivals lines peerLines i = none
      cases hs : sourceA service d arrivals lines peerLines i with
      | none => rfl
      | some x =>
        obtain ⟨-, al, hal, hc⟩ := sourceA_cases hs
        have hl0 : lines[i]? = some l := hl
        rw [hal] at hl0
        cases hl0
        rcases hc with ⟨_, _, _, hb1, -, hu, -⟩ | ⟨_, _, _, _, _, _, hb1, -⟩ | hpf
        · rw [hb] at hb1
          cases hb1
          rw [unreached_of hal hb hk] at hu
          cases hu
        · rw [hb] at hb1
          cases hb1
        · exact absurd hb ((notAnswerFrom hal hpf).1 _ _ _)
    · show sourceB inputs peerLines i = none
      cases hs : sourceB inputs peerLines i with
      | none => rfl
      | some x =>
        obtain ⟨s, j⟩ := x
        obtain ⟨rfl, -⟩ := sourceB_spec hs
        obtain ⟨_, l1, -, hl1, -, -, -, hna, -⟩ := fromB _ _ hs
        have hl1' : peerLines[i]? = some l := hl
        rw [hl1] at hl1'
        cases hl1'
        have := hna _ _ _ hb
        simp [Answer.unavailable, hk] at this
    · rfl
  · intro r s i l id to a hsr hslen hl hb ht hu
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : lines[i]? = some l := hl
        have ht' : (peerTarget? d.peer lines to).isSome := ht
        have hu' : unreached lines to = false := hu
        obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp ht'
        obtain ⟨t, b, hb', -, -⟩ := mocked_answer_given h hl0 hb htarget hu'
        obtain ⟨j, bl, id', hbl, hbb, -, hk⟩ := answersTo_getElem? hb'
        obtain ⟨hj, hbl⟩ := getElem?_take_some hbl
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hk
        have hex : ∃ j, j < peerBefore arrivals peerLines i ∧
            AnswerAt peerLines .out to (answersTo (lines.take i) .in to).length j :=
          ⟨j, hj, bl, id', b, hbl, hbb, hk⟩
        refine ⟨hex.choose, ?_⟩
        show sourceA service d arrivals lines peerLines i = some (1, hex.choose)
        unfold sourceA
        simp only [hl0, hb]
        rw [ite_eq_left ⟨ht', hu'⟩, dite_eq_left hex]
      · omega
    · obtain _ | _ | s := s
      · have ht' : (peerTarget? service peerLines to).isSome := ht
        exact sourceOfIn hl (by simp [hb, TraceLine.Body.dir]) fun st hw => by
          obtain ⟨target, hr, hreq⟩ := (writes_received hw).2 _ _ _ hb
          exact ⟨target, hr, by simpa [peerTarget?, hreq] using ht'⟩
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)
  · intro r s i l id name n payload resultOf hsr hslen hl hb hn
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : lines[i]? = some l := hl
        have hn' : peerName? d.peer name = some n := hn
        have hex := received_event_emitted h hl0 hb hn'
        refine ⟨hex.choose, ?_⟩
        show sourceA service d arrivals lines peerLines i = some (1, hex.choose)
        unfold sourceA
        simp only [hl0, hb, hn']
        rw [dite_eq_left hex]
      · omega
    · obtain _ | _ | s := s
      · have hn' : peerName? service name = some n := hn
        exact sourceOfIn hl (by simp [hb, TraceLine.Body.dir]) fun st hw =>
          ⟨name, (writes_received hw).1 _ _ _ _ hb, by simp [hn']⟩
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)
  · intro r s i l hsr hslen hl hsend
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : lines[i]? = some l := hl
        have hsend' : (peerBody? d.peer lines [] l).isSome := hsend
        rw [← peerBody_isSome (keys := peerForward service d arrivals lines peerLines i)]
          at hsend'
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsend'
        obtain ⟨k, hk⟩ :=
          List.mem_iff_getElem?.mp (peerInputs_line_mem (d := d) hl0 hb)
        have hkm : (inputs.map (·.1))[k]? = some ⟨l.time, b, none, none, none, none⟩ := by
          rw [List.getElem?_map, show inputs[k]? = _ from hk]
          rfl
        obtain ⟨p, hp⟩ := runOf_isSome hrun hkm
        obtain ⟨j, hj⟩ := deliveredAt_of hk hp
        exact ⟨j, sourceB_of hj⟩
      · omega
    · obtain _ | _ | s := s
      · have hl1 : peerLines[i]? = some l := hl
        obtain ⟨i', hp⟩ := hsent i l hl1 hsend
        obtain ⟨al, bl, hal, -, -, hS⟩ := notFrom hp
        obtain ⟨-, ha, he, -⟩ := hS.request
        refine ⟨i', ?_⟩
        show sourceA service d arrivals lines peerLines i' = some (1, i)
        unfold sourceA
        rw [hal]
        dsimp only
        split
        · next hb => exact absurd hb (ha _ _ _)
        · next hb => exact absurd hb (he _ _ _ _)
        · rw [hp]
          rfl
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)
  · intro r i s j i' j' hs hj hs'
    obtain _ | _ | r := r
    · obtain ⟨rfl, -⟩ := sourceA_cases hs
      obtain ⟨-, hd⟩ := sourceB_spec hs'
      obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec hd
      obtain ⟨al', -, hal', -, hout, -⟩ := fromB j' i' hs'
      obtain ⟨al, hal, hin⟩ := inOf i _ _ hs
      have hle := arrival_le hlen (Nat.lt_of_le_of_lt hj (beforeOf i _ _ hs)) hl (arrivals_of_line hk)
      have hne : i' ≠ i := by
        rintro rfl
        rw [hal] at hal'
        cases hal'
        rw [hin] at hout
        cases hout
      omega
    · obtain ⟨rfl, hd⟩ := sourceB_spec hs
      obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec hd
      obtain ⟨al, -, hal, -, hout, -⟩ := fromB i j hs
      obtain ⟨al', hal', hin⟩ := inOf j' _ _ hs'
      have hne : j' ≠ j := by
        rintro rfl
        rw [hal] at hal'
        cases hal'
        rw [hin] at hout
        cases hout
      exact Nat.lt_of_lt_of_le (beforeOf j' _ _ hs') (before_le hlen hl (arrivals_of_line hk) (by omega))
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)

end Tazuna.Thm.Sim.PeerNetwork
