import Tazuna.Semantics.Network
import Tazuna.Thm.Semantics.System.PeerCheck

/-!
Stage 2 of the check of a scenario's mocks of a peer (network_realizes): when the check finds no violation, the
scenario's run and the peer's run form an execution on a well formed network. The execution is built from the two runs
directly: a request or an answer reaches the peer at the time the scenario sends it, and an answer, event or request
reaches the scenario at the time the scenario takes it.
-/

namespace Tazuna.Thm.Semantics.Network

open Tazuna.Data Tazuna.Thm.Data.Trace Tazuna.Thm.Data.Unify Tazuna.Semantics Tazuna.Semantics.Network Tazuna.Thm.Semantics.System.PeerCheck Tazuna.Thm.Verify.Matching

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

theorem runOf_isSome {canon : Schema → Value → Value} {inputs : List Step} {lines : List TraceLine} {k : Nat}
    {x : Step} (h : RunOf canon inputs lines) (hx : inputs[k]? = some x) : ∃ p, (inLines lines)[k]? = some p := by
  have hk := (List.getElem?_eq_some_iff.mp hx).1
  rw [h.1] at hk
  exact ⟨_, List.getElem?_eq_getElem hk⟩

theorem mem_peerInputs_line {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} {st : Step} {i : Nat}
    (h : (st, PeerOrigin.line i) ∈ peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines) :
    ∃ l b, lines[i]? = some l ∧
      peerInput? service peer received fromLines lines (peerForward peerForm ownInputForm service peer fromLines (peerArrivals service peer received fromLines state elsewhere lines) lines peerLines i) l = some b ∧
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

theorem peerInputs_line_mem {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} {i : Nat} {l : TraceLine}
    {b : Step.Body} (hi : lines[i]? = some l)
    (hb : peerBody? peer lines (peerForward peerForm ownInputForm service peer fromLines (peerArrivals service peer received fromLines state elsewhere lines) lines peerLines i) l = some b) :
    (⟨l.time, b, none, none, none⟩, PeerOrigin.line i) ∈
      peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap]
  refine .inr ⟨(⟨l.time, b, none, none, none⟩, PeerOrigin.line i), ⟨i, ?_, .inr ?_⟩, rfl⟩
  · have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.mem_range]
    omega
  · simp [hi, hb, peerInput?]

/-- The line of the scenario's run that an input of the peer comes from. -/
def _root_.Tazuna.Semantics.PeerOrigin.line? : PeerOrigin → Option Nat
  | .line i => some i
  | _ => none

theorem pairwise_flatMap_single {f : Nat → List Nat} {l : List Nat} (hl : l.Pairwise (· < ·))
    (h : ∀ n, ∀ m ∈ f n, m = n) (h1 : ∀ n, (f n).length ≤ 1) : (l.flatMap f).Pairwise (· < ·) := by
  refine List.pairwise_flatMap.mpr ⟨fun n _ => ?_, hl.imp fun hlt => ?_⟩
  · have := h1 n
    match hf : f n with
    | [] => exact List.Pairwise.nil
    | [_] => simp
    | _ :: _ :: _ => rw [hf] at this; simp at this
  · intro x hx y hy
    rw [h _ x hx, h _ y hy]
    exact hlt

theorem peerInputs_lines_pairwise {peerForm ownInputForm : String → Value → CValue} {service peer : String}
    {received : List String} {fromLines : List Nat} {state : List Step} {elsewhere : List (Nat × Step)}
    {lines peerLines : List TraceLine} :
    ((peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines).filterMap
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

theorem peerInputs_lines_nodup {peerForm ownInputForm : String → Value → CValue} {service peer : String}
    {received : List String} {fromLines : List Nat} {state : List Step} {elsewhere : List (Nat × Step)}
    {lines peerLines : List TraceLine} :
    ((peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines).filterMap
      (·.2.line?)).Nodup :=
  peerInputs_lines_pairwise.imp Nat.ne_of_lt

theorem peerBody_isSome {peer : String} {lines : List TraceLine} {keys : Bindings} {l : TraceLine} :
    (peerBody? peer lines keys l).isSome = (peerBody? peer lines [] l).isSome := by
  simp only [peerBody?]
  split <;> simp

theorem peerEvent_isSome {service : String} {received : List String} {keys : Bindings} {l : TraceLine} :
    (peerEvent? service received keys l).isSome = (peerEvent? service received [] l).isSome := by
  simp only [peerEvent?]
  split <;> simp

theorem peerAnswer_isSome {service : String} {lines : List TraceLine} {fromLines : List Nat} {keys : Bindings}
    {l : TraceLine} :
    (peerAnswer? service lines fromLines keys l).isSome = (peerAnswer? service lines fromLines [] l).isSome := by
  simp only [peerAnswer?]
  split
  · split
    · rfl
    · rw [Option.isSome_map, Option.isSome_map]
  · rfl

theorem peerInput_isSome {service peer : String} {received : List String} {fromLines : List Nat}
    {lines : List TraceLine} {keys : Bindings} {l : TraceLine} :
    (peerInput? service peer received fromLines lines keys l).isSome =
      (peerInput? service peer received fromLines lines [] l).isSome := by
  have hb := peerBody_isSome (peer := peer) (lines := lines) (keys := keys) (l := l)
  have he := peerEvent_isSome (service := service) (received := received) (keys := keys) (l := l)
  have ha := peerAnswer_isSome (service := service) (lines := lines) (fromLines := fromLines) (keys := keys) (l := l)
  simp only [peerInput?]
  cases h1 : peerBody? peer lines keys l <;> cases h2 : peerBody? peer lines [] l <;>
    cases h3 : peerEvent? service received keys l <;> cases h4 : peerEvent? service received [] l <;>
    cases h5 : peerAnswer? service lines fromLines keys l <;> cases h6 : peerAnswer? service lines fromLines [] l <;>
    simp_all [Option.orElse]

/-- The origins of peerPlaced do not depend on the strings that the inputs take. -/
theorem peerPlaced_origins {service peer : String} {received : List String} {fromLines : List Nat} {elsewhere : List (Nat × Step)}
    {lines : List TraceLine} (f g : Nat → Bindings) :
    (peerPlaced service peer received fromLines elsewhere lines f).map (·.2) =
      (peerPlaced service peer received fromLines elsewhere lines g).map (·.2) := by
  simp only [peerPlaced, List.map_flatMap, List.map_append]
  congr 1
  funext n
  congr 1
  split
  · next l _ =>
    have hf := peerInput_isSome (service := service) (peer := peer) (received := received) (fromLines := fromLines)
      (lines := lines) (keys := f n) (l := l)
    have hg := peerInput_isSome (service := service) (peer := peer) (received := received) (fromLines := fromLines)
      (lines := lines) (keys := g n) (l := l)
    cases h1 : peerInput? service peer received fromLines lines (f n) l <;>
      cases h2 : peerInput? service peer received fromLines lines (g n) l <;> simp_all
  · rfl

/-- The arrivals of the peer's inputs are those of peerArrivals. -/
theorem peerInputs_arrivals {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} :
    (peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines).map (·.2.arrival elsewhere) =
      peerArrivals service peer received fromLines state elsewhere lines := by
  have key : ∀ f g, (peerPlaced service peer received fromLines elsewhere lines f).map (·.2.arrival elsewhere) =
      (peerPlaced service peer received fromLines elsewhere lines g).map (·.2.arrival elsewhere) := fun f g => by
    have := congrArg (List.map (PeerOrigin.arrival elsewhere)) (peerPlaced_origins (service := service) (peer := peer)
      (received := received) (fromLines := fromLines) (elsewhere := elsewhere) (lines := lines) f g)
    simpa only [List.map_map, Function.comp_def] using this
  simp only [peerInputs, peerArrivals, List.map_append, List.map_map]
  congr 1
  refine Eq.trans (List.map_congr_left fun ⟨_, o⟩ _ => ?_) (key _ _)
  cases o <;> rfl

theorem arrivals_of_line {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} {k n : Nat} {st : Step}
    (h : (peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines)[k]? = some (st, PeerOrigin.line n)) :
    (peerArrivals service peer received fromLines state elsewhere lines)[k]? = some n := by
  rw [← peerInputs_arrivals (peerForm := peerForm) (peerLines := peerLines), List.getElem?_map, h]
  rfl

theorem inLines_le {lines : List TraceLine} {k k' j j' : Nat} {l l' : TraceLine}
    (h : (inLines lines)[k]? = some (l, j)) (h' : (inLines lines)[k']? = some (l', j')) (hk : k ≤ k') : j ≤ j' := by
  have hp : ((inLines lines).map Prod.snd).Pairwise (· < ·) := by
    refine List.Pairwise.sublist (List.filter_sublist.map _) ?_
    rw [List.zipIdx_map_snd]
    exact List.pairwise_lt_range'
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨hl', he'⟩ := List.getElem?_eq_some_iff.mp h'
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · have := List.pairwise_iff_getElem.mp hp k k' (by simpa using hl) (by simpa using hl') hlt
    simp only [List.getElem_map, he, he'] at this
    exact Nat.le_of_lt this
  · rw [he] at he'
    cases he'
    exact Nat.le_refl _

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

/--
The peer's `in` line for a request or end of subscription of the scenario's run carries that line, at the same time.
-/
theorem peerBody_carries {agree : Agree} {ids : Ids} {e : Execution} {canon : Schema → Value → Value} {peer : String}
    {lines peerLines : List TraceLine} {keys : Bindings} {i : Nat} {al l : TraceLine} {b : Step.Body}
    (hname : e.name 1 = peer) (hagree : ∀ sch x, agree (0, i) 1 sch x (canon sch (keys.rename x)))
    (hids : ∀ x, ids (0, i) 1 x x)
    (hb : peerBody? peer lines keys al = some b) (hw : Writes canon peerLines ⟨al.time, b, none, none, none⟩ l) :
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
    (hb : peerEvent? service received keys al = some b) (hw : Writes canon peerLines ⟨al.time, b, none, none, none⟩ l) :
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

theorem peerName_traceName (p n : String) : peerName? p s!"{p}.{n}" = some n := by
  simp only [peerName?, toString]
  simp
  apply String.toList_inj.mp
  simp [String.toList_append, ← String.length_toList]

theorem AnswerCarries.mapOutput {P : Value → Value → Prop} {f : Value → Value} (h : ∀ x, P x (f x)) :
    ∀ a : Answer, AnswerCarries P a (a.mapOutput f)
  | .accepted (some x) => h x
  | .accepted none => trivial
  | .fulfilled x => h x
  | .rejected _ => rfl

theorem unavailable_mapOutput {f : Value → Value} : ∀ a : Answer, (a.mapOutput f).unavailable = a.unavailable
  | .accepted _ | .fulfilled _ | .rejected _ => rfl

theorem mapOutput_mapOutput {f g : Value → Value} : ∀ a : Answer, (a.mapOutput f).mapOutput g = a.mapOutput (g ∘ f)
  | .accepted none | .accepted (some _) | .fulfilled _ | .rejected _ => rfl

/-- The peer's `in` line for an answer to its request of a from line carries the scenario's answer, at the same time. -/
theorem peerAnswer_carries {agree : Agree} {ids : Ids} {e : Execution} {canon : Schema → Value → Value}
    {service : String} {lines peerLines : List TraceLine} {fromLines : List Nat} {keys : Bindings} {i : Nat}
    {al l : TraceLine} {b : Step.Body}
    (hname : e.name 0 = service) (hlines : e.lines 1 = peerLines)
    (hagree : ∀ sch x, agree (0, i) 1 sch x (canon sch (keys.rename x)))
    (hids : ∀ x, ids (0, i) 1 x ((keys.lookup x).getD x))
    (hb : peerAnswer? service lines fromLines keys al = some b) (hw : Writes canon peerLines ⟨al.time, b, none, none, none⟩ l) :
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
    (hw : Writes canon peerLines ⟨al.time, b, none, none, none⟩ l) :
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

theorem peerInputs_line_unique {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} {k k' i : Nat}
    {x x' : Step} (hk : (peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines)[k]? = some (x, .line i))
    (hk' : (peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines)[k']? = some (x', .line i)) :
    k = k' :=
  index_unique (f := (·.2.line?)) peerInputs_lines_nodup hk hk' rfl rfl

theorem mem_peerInputs_given {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} {st : Step}
    (h : (st, PeerOrigin.given) ∈ peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines) : st ∈ state := by
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

theorem mem_peerInputs_elsewhere {peerForm ownInputForm : String → Value → CValue} {service peer : String} {received : List String} {fromLines : List Nat}
    {state : List Step} {elsewhere : List (Nat × Step)} {lines peerLines : List TraceLine} {st : Step} {k : Nat}
    (h : (st, PeerOrigin.elsewhere k) ∈ peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines) :
    ∃ s ∈ elsewhere.map (·.2), ∃ keys, st.body = s.body.forPeer keys := by
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

theorem forPeer_received {b : Step.Body} {keys : Bindings} : (b.forPeer keys).received? = b.received? := by
  cases b <;> rfl

theorem inLines_of {lines : List TraceLine} {i : Nat} {l : TraceLine} (hl : lines[i]? = some l)
    (hd : l.body.dir = .in) : ∃ k : Nat, (inLines lines)[k]? = some (l, i) := by
  have hm : (l, i) ∈ inLines lines := by
    simp only [inLines, List.mem_filter, beq_iff_eq]
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hl, hd⟩
  exact List.mem_iff_getElem?.mp hm

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

theorem unreached_of {lines : List TraceLine} {i : Nat} {l : TraceLine} {id : String} {to : String}
    {rejection : Rejection} (hl : lines[i]? = some l) (hb : l.body = .answer .in id to (.rejected rejection))
    (hk : rejection.kind = .unavailable) : unreached lines to = true := by
  simp only [unreached, List.any_eq_true]
  exact ⟨l, List.mem_of_getElem? hl, by simp [hb, hk]⟩

theorem requestOf_some {d : Dir} {b : TraceLine.Body} {t id name : String} {x : Value}
    (h : requestOf? d b = some (t, id, name, x)) :
    (b = .command d id name x ∧ t = "command") ∨ (b = .query d id name x ∧ t = "query") ∨
      (b = .subscribe d id name x ∧ t = "subscribe") := by
  cases b <;> simp only [requestOf?] at h
  all_goals first
    | (split at h
       · next hd =>
         simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨h1, rfl, rfl, rfl⟩ := h
         simp only [beq_iff_eq] at hd
         subst hd h1
         first | exact .inl ⟨rfl, rfl⟩ | exact .inr (.inl ⟨rfl, rfl⟩) | exact .inr (.inr ⟨rfl, rfl⟩)
       · cases h)
    | cases h

/-- A line that a from line pairs (SentAs) is an `in` request or end of a subscription. -/
theorem _root_.Tazuna.Thm.Semantics.System.PeerCheck.SentAs.request {c : List String} {seen form : String → Value → CValue} {service : String}
    {bs bs' : Bindings} {l b : TraceLine} (h : SentAs c seen form service bs bs' l b) :
    l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      (∀ id name p r, l.body ≠ .event .in id name p r) ∧ b.body.dir = .out ∧ isEventLine b = false ∧
      (∀ id to a, b.body ≠ .answer .out id to a) := by
  rcases h.body with ⟨t, id, name, x, id', m, y, hx, hy, -, -⟩ | ⟨id, to, id', to', hl, hb⟩
  · rcases requestOf_some hx with ⟨hl, -⟩ | ⟨hl, -⟩ | ⟨hl, -⟩ <;>
    rcases requestOf_some hy with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;>
    simp [hl, hb, TraceLine.Body.dir, isEventLine]
  · simp [hl, hb, TraceLine.Body.dir, isEventLine]

variable {peerForm ownInputForm : String → Value → CValue} {service peer : String} {fromLines arrivals : List Nat}
  {lines peerLines : List TraceLine}

/-- The check of a from line pairs it with the line that peerSent finds. -/
theorem peerLine_paired {bs bs' bs'' : Bindings} {i j : Nat} {l : TraceLine}
    (hc : fromLines.contains i = true)
    (hs : peerSent (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service bs
      (peerLines.take (peerBefore arrivals peerLines i)) l = .ok (j, bs'))
    (h : peerLine peerForm ownInputForm service peer fromLines arrivals lines peerLines bs i l = .ok bs'') : bs'' = bs' := by
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
def peerPaired? (peerForm ownInputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (lines peerLines : List TraceLine) (i : Nat) : Option Nat :=
  if fromLines.contains i then
    (lines[i]?.bind fun l => (peerSent (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
      (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i)
      (peerLines.take (peerBefore arrivals peerLines i)) l).toOption).map (·.1)
  else none

/--
With no violation, the peer's line that sends the scenario's from line `i` comes before the peer takes an input that
arrives after the line, and the check binds its id to the line's (SentAs).
-/
theorem paired_spec {halted : Option (PeerOrigin × String)} {i j : Nat}
    (h : peerFindings peerForm ownInputForm service peer fromLines arrivals lines peerLines halted = [])
    (hp : peerPaired? peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some j) :
    ∃ al bl, lines[i]? = some al ∧ peerLines[j]? = some bl ∧ j < peerBefore arrivals peerLines i ∧
      SentAs (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
        (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i)
        (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1)) al bl := by
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
      have hs' : peerSent (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
          (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i)
          (peerLines.take (peerBefore arrivals peerLines i)) al = .ok (j', bs') := by
        revert hs
        cases peerSent (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
          (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i)
          (peerLines.take (peerBefore arrivals peerLines i)) al <;> simp [Except.toOption]
      obtain ⟨bl, hbl, hS⟩ := peerSent_spec hs'
      obtain ⟨hj, hbl⟩ := getElem?_take_some hbl
      have heq := peerLine_paired hc hs' (peerLine_ok h hal)
      rw [heq]
      exact ⟨al, bl, rfl, hbl, hj, hS⟩
  · cases hp

open Classical in
/--
The line of the peer's run that the scenario's line `i` received: the peer's answer at the same place for a mocked
answer to a request to the peer that reached it, a line that emits the event for a received event of the peer, before
the peer takes an input that arrives after the line (peerBefore), and the line that sends a from line (peerPaired?).
-/
noncomputable def sourceA (peerForm ownInputForm : String → Value → CValue) (service peer : String)
    (fromLines arrivals : List Nat) (lines peerLines : List TraceLine) (i : Nat) : Option Place :=
  match lines[i]? with
  | some l =>
    match l.body with
    | .answer .in _ to _ =>
      if (peerTarget? peer lines to).isSome ∧ unreached lines to = false then
        if h : ∃ j, j < peerBefore arrivals peerLines i ∧ AnswerAt peerLines .out to (answersTo (lines.take i) .in to).length j
        then some (1, h.choose)
        else none
      else none
    | .event .in _ name payload resultOf =>
      match peerName? peer name with
      | some n =>
        if h : ∃ j b, peerLines[j]? = some b ∧ j < peerBefore arrivals peerLines i ∧ PeerEmits peerForm service lines peerLines
            (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines) n payload resultOf l.time b then
          some (1, h.choose)
        else none
      | none => none
    | _ => (peerPaired? peerForm ownInputForm service peer fromLines arrivals lines peerLines i).map (1, ·)
  | none => none

theorem sourceA_cases {i s j : Nat}
    (h : sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some (s, j)) :
    s = 1 ∧ ∃ al, lines[i]? = some al ∧
      ((∃ id to a, al.body = .answer .in id to a ∧ (peerTarget? peer lines to).isSome ∧
          unreached lines to = false ∧ AnswerAt peerLines .out to (answersTo (lines.take i) .in to).length j ∧
          j < peerBefore arrivals peerLines i) ∨
        (∃ id name payload resultOf n bl, al.body = .event .in id name payload resultOf ∧
          peerName? peer name = some n ∧ peerLines[j]? = some bl ∧ j < peerBefore arrivals peerLines i ∧
          PeerEmits peerForm service lines peerLines (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines)
            n payload resultOf al.time bl) ∨
        peerPaired? peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some j) := by
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

theorem peerInputs_lines_lt {received : List String} {state : List Step} {elsewhere : List (Nat × Step)} {k k' i i' : Nat}
    {x x' : Step}
    (hk : (peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines)[k]? = some (x, .line i))
    (hk' : (peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines)[k']? =
      some (x', .line i')) (hlt : k < k') : i < i' :=
  filterMap_lt (f := (·.2.line?)) peerInputs_lines_pairwise hk hk' rfl rfl hlt

/--
How the scenario's service `service`, member 0, and its peer `peer`, member 1, see each other's values. The peer
receives a value of a request, event or answer of the scenario's line `i` in the form `canon` that its run writes, with
the strings that the peer takes in place of the scenario's before that line (peerForward); the scenario's service
receives an input of a request whose `ownInputForm` stands for the peer's, and a value of an answer or event that stands
for the peer's (PeerSees), under the final bindings.
-/
def peerAgree (peerForm ownInputForm : String → Value → CValue) (canon : Schema → Value → Value) (service peer : String)
    (fromLines arrivals : List Nat) (lines peerLines : List TraceLine) : Agree
  | (0, i), 1, sch, x, y => y = canon sch ((peerForward peerForm ownInputForm service peer fromLines arrivals lines peerLines i).rename x)
  | (1, _), 0, .input m, x, y =>
    ValueMatches (standsFor (createdOf peerLines) (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines))
      (seenInputOf ownInputForm service lines m x) (ownInputForm m y)
  | (1, _), 0, .output m, x, y | (1, _), 0, .payload m, x, y => ∃ n, peerName? peer m = some n ∧
    PeerSees peerForm service lines peerLines (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines) n x y
  | _, _, _, _, _ => False

/--
How the two members name each other's requests: the peer names a request of the scenario's line `n`, or the request of
an answer, by the same id or the one that the strings of the line take (peerForward), and the scenario's service names
a request of the peer by the same id or the one that the final bindings bind it to.
-/
def peerIds (peerForm ownInputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (lines peerLines : List TraceLine) : Ids
  | (0, n), 1, i, j => j = i ∨ (peerForward peerForm ownInputForm service peer fromLines arrivals lines peerLines n).lookup i = some j
  | (1, _), 0, i, j => j = i ∨ (peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines).lookup i = some j
  | _, _, _, _ => False

/--
Stage 2 of the check of a scenario's mocks of a peer. Let `lines` be the scenario's run of the service `service`, and
`peerLines` a run of the peer `peer` whose `in` lines are those that a run writes for the derived inputs (peerInputs), and
whose every request and end of a subscription to `service` is one that a from line of `fromLines` takes (peerPaired?).
Nothing checks this, and a peer's run can send `service` requests that no from line takes; the check neither delivers
them nor compares them. The given state and the elsewhere inputs give the peer no event of `service` and no answer to
a request to it. When the check finds no violation, an execution of the two runs on a well formed network exists: each
request of the scenario's run to the peer that reached it, and each answer to a request of a from line, arrives at the
peer at its send time; each event of `service` that the peer receives comes from the scenario's run at its emit time;
and each mocked answer, received event of the peer, and request of a from line comes from the peer's run, sent at or
before the time the scenario takes it and before the peer receives a line that the scenario sends after it
(WellFormed.causal), with the values and ids that the two runs see (peerAgree, peerIds).
-/
theorem network_realizes {canon : Schema → Value → Value} {received : List String} {state : List Step}
    {elsewhere : List (Nat × Step)} {halted : Option (PeerOrigin × String)}
    (hrun : RunOf canon ((peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines).map
      (·.1)) peerLines)
    (hsent : ∀ j l, peerLines[j]? = some l → Sends service peerLines l →
      ∃ i, peerPaired? peerForm ownInputForm service peer fromLines
        (peerArrivals service peer received fromLines state elsewhere lines) lines peerLines i = some j)
    (hown : ∀ s ∈ state ++ elsewhere.map (·.2), ∀ n, s.body.received? = some n → peerName? service n = none)
    (h : peerFindings peerForm ownInputForm service peer fromLines
      (peerArrivals service peer received fromLines state elsewhere lines) lines peerLines halted = []) :
    ∃ source, WellFormed
      (peerAgree peerForm ownInputForm canon service peer fromLines
        (peerArrivals service peer received fromLines state elsewhere lines) lines peerLines)
      (peerIds peerForm ownInputForm service peer fromLines
        (peerArrivals service peer received fromLines state elsewhere lines) lines peerLines)
      ⟨[(service, lines), (peer, peerLines)], source⟩ := by
  let arrivals := peerArrivals service peer received fromLines state elsewhere lines
  let inputs := peerInputs peerForm ownInputForm service peer received fromLines state elsewhere lines peerLines
  let agree := peerAgree peerForm ownInputForm canon service peer fromLines arrivals lines peerLines
  let ids := peerIds peerForm ownInputForm service peer fromLines arrivals lines peerLines
  let final := peerFinal peerForm ownInputForm service peer fromLines arrivals lines peerLines
  let source : Place → Option Place
    | (0, i) => sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i
    | (1, j) => sourceB inputs peerLines j
    | _ => none
  let e : Execution := ⟨[(service, lines), (peer, peerLines)], source⟩
  have hname0 : e.name 0 = service := rfl
  have hname1 : e.name 1 = peer := rfl
  have hlines1 : e.lines 1 = peerLines := rfl
  have hline2 : ∀ m j, e.line? (m + 1 + 1, j) = none := fun _ _ => by
    simp [Execution.line?, Execution.lines, e]
  have hsrc2 : ∀ m j, e.source (m + 1 + 1, j) = none := fun _ _ => rfl
  have hmembers : e.members.length = 2 := rfl
  have toFinal : ∀ {i : Nat} {l : TraceLine}, lines[i]? = some l →
      peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1) <+: final :=
    fun hi => final_of hi
  have notFrom : ∀ {i j : Nat}, peerPaired? peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some j →
      ∃ al bl, lines[i]? = some al ∧ peerLines[j]? = some bl ∧ j < peerBefore arrivals peerLines i ∧
        SentAs (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
          (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i)
          (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1)) al bl :=
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
    cases hx : (peerForward peerForm ownInputForm service peer fromLines arrivals lines peerLines i).lookup x with
    | none => exact .inl rfl
    | some y => exact .inr (by rw [hx]; rfl)
  have fromA : ∀ i s j, sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some (s, j) →
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
    show (peerArrivals service peer received fromLines state elsewhere lines).length = _
    rw [← peerInputs_arrivals (peerForm := peerForm) (ownInputForm := ownInputForm) (peerLines := peerLines), List.length_map,
      ← hrun.1, List.length_map]
  have inOf : ∀ i s j, sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some (s, j) →
      ∃ al, lines[i]? = some al ∧ al.body.dir = .in := by
    intro i s j hs
    obtain ⟨al, -, hal, -, -, hin, -⟩ := fromA i s j hs
    exact ⟨al, hal, hin⟩
  have beforeOf : ∀ i s j, sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some (s, j) →
      j < peerBefore arrivals peerLines i := by
    intro i s j hs
    obtain ⟨_, al, hal, hc⟩ := sourceA_cases hs
    rcases hc with ⟨_, _, _, _, _, _, _, hj⟩ | ⟨_, _, _, _, _, _, _, _, _, hj, _⟩ | hp
    · exact hj
    · exact hj
    · obtain ⟨_, _, _, _, hj, _⟩ := notFrom hp
      exact hj
  have notAnswerFrom : ∀ {i j : Nat} {al : TraceLine}, lines[i]? = some al →
      peerPaired? peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some j →
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
                SentAs (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
                  (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i)
                  (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i + 1)) al sent →
                SentAs (createdOf peerLines) (seenInputOf ownInputForm service lines) ownInputForm service
                  (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines i')
                  (peerBindings peerForm ownInputForm service peer fromLines arrivals lines peerLines (i' + 1)) al' sent →
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
    · show sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = none
      cases hs : sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i with
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
        have ht' : (peerTarget? peer lines to).isSome := ht
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
        show sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some (1, hex.choose)
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
        have hn' : peerName? peer name = some n := hn
        have hex := received_event_emitted h hl0 hb hn'
        refine ⟨hex.choose, ?_⟩
        show sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i = some (1, hex.choose)
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
        have hsend' : (peerBody? peer lines [] l).isSome := hsend
        rw [← peerBody_isSome (keys := peerForward peerForm ownInputForm service peer fromLines arrivals lines peerLines i)]
          at hsend'
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsend'
        obtain ⟨k, hk⟩ :=
          List.mem_iff_getElem?.mp (peerInputs_line_mem (state := state) (elsewhere := elsewhere) hl0 hb)
        have hkm : (inputs.map (·.1))[k]? = some ⟨l.time, b, none, none, none⟩ := by
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
        show sourceA peerForm ownInputForm service peer fromLines arrivals lines peerLines i' = some (1, i)
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

end Tazuna.Thm.Semantics.Network
