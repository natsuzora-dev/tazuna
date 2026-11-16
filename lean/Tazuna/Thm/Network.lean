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

theorem runOf_isSome {canon : String → Value → Value} {inputs : List Step} {lines : List TraceLine} {k : Nat}
    {x : Step} (h : RunOf canon inputs lines) (hx : inputs[k]? = some x) : ∃ p, (inLines lines)[k]? = some p := by
  have hk := (List.getElem?_eq_some_iff.mp hx).1
  rw [h.1] at hk
  exact ⟨_, List.getElem?_eq_getElem hk⟩

/-- The peer's input of the run's line `l`, given the strings `keys` that the peer takes (peerInputs). -/
abbrev peerInput? (service peer : String) (received : List String) (lines : List TraceLine) (keys : Bindings)
    (l : TraceLine) : Option Step.Body :=
  (peerBody? peer lines keys l).orElse fun _ => peerEvent? service received keys l

theorem mem_peerInputs_line {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {st : Step} {i : Nat}
    (h : (st, Origin.line i) ∈ peerInputs normal service peer received state elsewhere aLines bLines) :
    ∃ l b, aLines[i]? = some l ∧
      peerInput? service peer received aLines (peerForward normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i) l = some b ∧
      st = ⟨l.time, b, none, none, none⟩ := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap] at h
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

theorem peerInputs_line_mem {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {i : Nat} {l : TraceLine}
    {b : Step.Body} (hi : aLines[i]? = some l)
    (hb : peerBody? peer aLines (peerForward normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i) l = some b) :
    (⟨l.time, b, none, none, none⟩, Origin.line i) ∈
      peerInputs normal service peer received state elsewhere aLines bLines := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap]
  refine .inr ⟨(⟨l.time, b, none, none, none⟩, Origin.line i), ⟨i, ?_, .inr ?_⟩, rfl⟩
  · have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.mem_range]
    omega
  · simp [hi, hb]

/-- The line of the scenario's run that an input of the peer comes from. -/
def _root_.Tazuna.Semantics.Origin.line? : Origin → Option Nat
  | .line i => some i
  | _ => none

theorem nodup_flatMap_single {f : Nat → List Nat} {l : List Nat} (hl : l.Nodup) (h : ∀ n, ∀ m ∈ f n, m = n)
    (h1 : ∀ n, (f n).length ≤ 1) : (l.flatMap f).Nodup := by
  refine List.pairwise_flatMap.mpr ⟨fun n _ => ?_, hl.imp fun hne => ?_⟩
  · have := h1 n
    match hf : f n with
    | [] => exact List.nodup_nil
    | [_] => simp
    | _ :: _ :: _ => rw [hf] at this; simp at this
  · intro x hx y hy hxy
    subst hxy
    exact hne ((h _ x hx).symm.trans (h _ x hy))

theorem peerInputs_lines_nodup {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} :
    ((peerInputs normal service peer received state elsewhere aLines bLines).filterMap (·.2.line?)).Nodup := by
  have hnone : ∀ {α : Type} (l : List α), l.filterMap (fun _ => (none : Option Nat)) = [] :=
    fun _ => List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
  simp only [peerInputs, peerPlaced, List.filterMap_append, List.filterMap_map, List.filterMap_flatMap, Function.comp_def,
    Origin.line?, hnone, List.nil_append]
  refine nodup_flatMap_single List.nodup_range (fun n m hm => ?_) (fun n => ?_)
  · split at hm
    · simp only [Option.toList_map, List.filterMap_map, Function.comp_def, List.mem_filterMap] at hm
      obtain ⟨_, _, hm⟩ := hm
      simpa using hm.symm
    · simp at hm
  · split
    · simp only [Option.toList_map, List.filterMap_map, Function.comp_def]
      refine Nat.le_trans (List.length_filterMap_le _ _) ?_
      generalize (Option.orElse _ _ : Option Step.Body) = o
      cases o <;> simp
    · simp

theorem peerBody_isSome {peer : String} {lines : List TraceLine} {keys : Bindings} {l : TraceLine} :
    (peerBody? peer lines keys l).isSome = (peerBody? peer lines [] l).isSome := by
  simp only [peerBody?]
  split <;> simp

theorem peerEvent_isSome {service : String} {received : List String} {keys : Bindings} {l : TraceLine} :
    (peerEvent? service received keys l).isSome = (peerEvent? service received [] l).isSome := by
  simp only [peerEvent?]
  split <;> simp

/-- The origins of peerPlaced do not depend on the strings that the inputs take. -/
theorem peerPlaced_origins {service peer : String} {received : List String} {elsewhere : List (Nat × Step)}
    {aLines : List TraceLine} (f g : Nat → Bindings) :
    (peerPlaced service peer received elsewhere aLines f).map (·.2) =
      (peerPlaced service peer received elsewhere aLines g).map (·.2) := by
  simp only [peerPlaced, List.map_flatMap, List.map_append]
  congr 1
  funext n
  congr 1
  split
  · next l _ =>
    have hb := peerBody_isSome (peer := peer) (lines := aLines) (keys := f n) (l := l)
    have hb' := peerBody_isSome (peer := peer) (lines := aLines) (keys := g n) (l := l)
    have he := peerEvent_isSome (service := service) (received := received) (keys := f n) (l := l)
    have he' := peerEvent_isSome (service := service) (received := received) (keys := g n) (l := l)
    cases h1 : peerBody? peer aLines (f n) l <;> cases h2 : peerBody? peer aLines (g n) l <;>
      cases h3 : peerEvent? service received (f n) l <;> cases h4 : peerEvent? service received (g n) l <;>
      simp_all [Option.orElse]
  · rfl

/-- The arrivals of the peer's inputs are those of peerArrivals. -/
theorem peerInputs_arrivals {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} :
    (peerInputs normal service peer received state elsewhere aLines bLines).map (·.2.arrival elsewhere) =
      peerArrivals service peer received state elsewhere aLines := by
  have key : ∀ f g, (peerPlaced service peer received elsewhere aLines f).map (·.2.arrival elsewhere) =
      (peerPlaced service peer received elsewhere aLines g).map (·.2.arrival elsewhere) := fun f g => by
    have := congrArg (List.map (Origin.arrival elsewhere)) (peerPlaced_origins (service := service) (peer := peer)
      (received := received) (elsewhere := elsewhere) (aLines := aLines) f g)
    simpa only [List.map_map, Function.comp_def] using this
  simp only [peerInputs, peerArrivals, List.map_append, List.map_map]
  congr 1
  refine Eq.trans (List.map_congr_left fun ⟨_, o⟩ _ => ?_) (key _ _)
  cases o <;> rfl

theorem arrivals_of_line {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {k n : Nat} {st : Step}
    (h : (peerInputs normal service peer received state elsewhere aLines bLines)[k]? = some (st, Origin.line n)) :
    (peerArrivals service peer received state elsewhere aLines)[k]? = some n := by
  rw [← peerInputs_arrivals (normal := normal) (bLines := bLines), List.getElem?_map, h]
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
theorem arrival_le {arrivals : List Nat} {bLines : List TraceLine} {i k j a : Nat} {l : TraceLine}
    (hlen : arrivals.length = (inLines bLines).length) (hj : j < peerBefore arrivals bLines i)
    (hk : (inLines bLines)[k]? = some (l, j)) (ha : arrivals[k]? = some a) : a ≤ i := by
  unfold peerBefore at hj
  cases hf : arrivals.findIdx? (i < ·) with
  | none =>
    have := (List.findIdx?_eq_none_iff.mp hf) a (List.mem_of_getElem? ha)
    simp only [decide_eq_false_iff_not, Nat.not_lt] at this
    exact this
  | some k0 =>
    rw [hf] at hj
    obtain ⟨hk0, -, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    obtain ⟨⟨l0, p0⟩, h0⟩ : ∃ x, (inLines bLines)[k0]? = some x :=
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
theorem before_le {arrivals : List Nat} {bLines : List TraceLine} {i k p a : Nat} {l : TraceLine}
    (hlen : arrivals.length = (inLines bLines).length) (hk : (inLines bLines)[k]? = some (l, p))
    (ha : arrivals[k]? = some a) (hi : i < a) : peerBefore arrivals bLines i ≤ p := by
  unfold peerBefore
  cases hf : arrivals.findIdx? (i < ·) with
  | none =>
    have := (List.findIdx?_eq_none_iff.mp hf) a (List.mem_of_getElem? ha)
    simp only [decide_eq_false_iff_not] at this
    exact absurd hi this
  | some k0 =>
    obtain ⟨hk0, -, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    obtain ⟨⟨l0, p0⟩, h0⟩ : ∃ x, (inLines bLines)[k0]? = some x :=
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
theorem peerBody_carries {agree : Agree} {e : Execution} {canon : String → Value → Value} {peer : String}
    {lines : List TraceLine} {keys : Bindings} {al l : TraceLine} {b : Step.Body}
    (hname : e.name 1 = peer) (hagree : ∀ n x, agree 0 1 n x (canon n (keys.rename x)))
    (hb : peerBody? peer lines keys al = some b) (hw : Writes canon ⟨al.time, b, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      Carries agree e 0 1 al l := by
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
    exact ⟨trivial, hn, hagree n x⟩
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨trivial, hn, hagree n x⟩
  next _ id name x hal =>
    simp only [Option.map_eq_some_iff, Option.ite_none_left_eq_some, Bool.not_eq_true] at hb
    obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hb
    obtain ⟨id', hl, hid⟩ := hw
    cases hid id rfl
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl, hname]
    exact ⟨trivial, hn, hagree n x⟩
  next _ _ to hal =>
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb
    obtain ⟨_, rfl⟩ := hb
    obtain ⟨id', hl⟩ := hw
    refine ⟨by simp [hal, TraceLine.Body.dir], ht, hd, by simp [hl], ?_⟩
    simp only [Carries, hal, hl]
  next => simp at hb

/-- The peer's `in` line for an event of the scenario's run carries that line, at the same time. -/
theorem peerEvent_carries {agree : Agree} {e : Execution} {canon : String → Value → Value} {service : String}
    {received : List String} {keys : Bindings} {al l : TraceLine} {b : Step.Body}
    (hname : e.name 0 = service) (hagree : ∀ n x, agree 0 1 n x (canon n (keys.rename x)))
    (hb : peerEvent? service received keys al = some b) (hw : Writes canon ⟨al.time, b, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      Carries agree e 0 1 al l := by
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
    exact ⟨hn, hagree m x⟩
  next => simp at hb

theorem peerInput_carries {agree : Agree} {e : Execution} {canon : String → Value → Value} {service peer : String}
    {received : List String} {lines : List TraceLine} {keys : Bindings} {al l : TraceLine} {b : Step.Body}
    (hname0 : e.name 0 = service) (hname1 : e.name 1 = peer)
    (hagree : ∀ n x, agree 0 1 n x (canon n (keys.rename x)))
    (hb : peerInput? service peer received lines keys al = some b) (hw : Writes canon ⟨al.time, b, none, none, none⟩ l) :
    al.body.dir = .out ∧ l.time = al.time ∧ l.body.dir = .in ∧ (∀ id to a, l.body ≠ .answer .in id to a) ∧
      Carries agree e 0 1 al l := by
  cases hp : peerBody? peer lines keys al with
  | some b' =>
    simp only [peerInput?, hp, Option.orElse_some, Option.some.injEq] at hb
    subst hb
    exact peerBody_carries hname1 hagree hp hw
  | none =>
    simp only [peerInput?, hp, Option.orElse_none] at hb
    exact peerEvent_carries hname0 hagree hb hw

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

theorem peerInputs_line_unique {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {k k' i : Nat}
    {x x' : Step} (hk : (peerInputs normal service peer received state elsewhere aLines bLines)[k]? = some (x, .line i))
    (hk' : (peerInputs normal service peer received state elsewhere aLines bLines)[k']? = some (x', .line i)) :
    k = k' :=
  index_unique (f := (·.2.line?)) peerInputs_lines_nodup hk hk' rfl rfl

theorem mem_peerInputs_given {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {st : Step}
    (h : (st, Origin.given) ∈ peerInputs normal service peer received state elsewhere aLines bLines) : st ∈ state := by
  simp only [peerInputs, peerPlaced, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ⟨s, hs, he⟩ | ⟨a, ⟨n, _, ha⟩, he⟩
  · simp only [Prod.mk.injEq] at he
    exact he.1 ▸ hs
  · exfalso
    rcases ha with ⟨_, _, rfl⟩ | ha
    · simp at he
    · cases hl : aLines[n]? with
      | none => simp [hl] at ha
      | some l =>
        simp only [hl, Option.mem_toList, Option.map_eq_some_iff] at ha
        obtain ⟨b, -, rfl⟩ := ha
        simp at he

theorem mem_peerInputs_elsewhere {normal : String → Value → CValue} {service peer : String} {received : List String}
    {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine} {st : Step} {k : Nat}
    (h : (st, Origin.elsewhere k) ∈ peerInputs normal service peer received state elsewhere aLines bLines) :
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
    · cases hl : aLines[n]? with
      | none => simp [hl] at ha
      | some l =>
        simp only [hl, Option.mem_toList, Option.map_eq_some_iff] at ha
        obtain ⟨b, -, rfl⟩ := ha
        simp at he

theorem forPeer_event {b : Step.Body} {keys : Bindings} {id : Option String} {name : String} {x : Value}
    {r : Option String} (h : b.forPeer keys = .event id name x r) :
    ∃ id' x' r', b = .event id' name x' r' := by
  cases b <;> simp_all [Step.Body.forPeer]

theorem inLines_of {lines : List TraceLine} {i : Nat} {l : TraceLine} (hl : lines[i]? = some l)
    (hd : l.body.dir = .in) : ∃ k : Nat, (inLines lines)[k]? = some (l, i) := by
  have hm : (l, i) ∈ inLines lines := by
    simp only [inLines, List.mem_filter, beq_iff_eq]
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hl, hd⟩
  exact List.mem_iff_getElem?.mp hm

/-- The input that a run writes an `in` event line for is an event of the same name. -/
theorem writes_event {canon : String → Value → Value} {st : Step} {l : TraceLine} {id : String}
    {name : String} {payload : Value} {resultOf : Option String} (hw : Writes canon st l)
    (hb : l.body = .event .in id name payload resultOf) : ∃ sid x r, st.body = .event sid name x r := by
  obtain ⟨-, -, hw⟩ := hw
  cases hs : st.body with
  | event sid n x r =>
    simp only [hs] at hw
    obtain ⟨_, _, hl, -⟩ := hw
    rw [hb] at hl
    cases hl
    exact ⟨sid, x, r, rfl⟩
  | command | query | subscribe =>
    simp only [hs] at hw
    obtain ⟨_, hl, -⟩ := hw
    rw [hb] at hl
    cases hl
  | unsubscribe =>
    simp only [hs] at hw
    obtain ⟨_, hl⟩ := hw
    rw [hb] at hl
    cases hl
  | _ =>
    simp only [hs] at hw
    simp [isEventLine, hb] at hw

theorem AnswerCarries.mono {P Q : Value → Value → Prop} (h : ∀ x y, P x y → Q x y) :
    ∀ {b a : Answer}, AnswerCarries P b a → AnswerCarries Q b a
  | .accepted (some _), .accepted (some _), hp => h _ _ hp
  | .accepted none, .accepted none, _ => trivial
  | .fulfilled _, .fulfilled _, hp => h _ _ hp
  | .rejected _, .rejected _, hp => hp

theorem peerTarget_none {p : String} {lines : List TraceLine}
    (h : ∀ l ∈ lines, isEventLine l = false → ∀ n, l.body.name? = some n → peerName? p n = none) (to : String) :
    peerTarget? p lines to = none := by
  cases hr : requestName? lines to with
  | none => simp [peerTarget?, hr]
  | some m =>
    simp only [peerTarget?, hr, Option.bind_some]
    obtain ⟨l, hl, hs⟩ := List.exists_of_findSome?_eq_some hr
    split at hs
    all_goals first
      | (split at hs
         · rename_i hb _
           cases hs
           exact h l hl (by simp [isEventLine, hb]) _ (by simp [hb, TraceLine.Body.name?])
         · cases hs)
      | cases hs

theorem peerBody_none {p : String} {lines : List TraceLine} {keys : Bindings} {l : TraceLine}
    (h : ∀ l ∈ lines, isEventLine l = false → ∀ n, l.body.name? = some n → peerName? p n = none) (hl : l ∈ lines) :
    peerBody? p lines keys l = none := by
  simp only [peerBody?]
  split
  all_goals first
    | rfl
    | (simp [peerTarget_none h]; done)
    | (rename_i hb
       simp only [Option.map_eq_none_iff, ite_eq_left_iff, Bool.not_eq_true]
       exact fun _ => h l hl (by simp [isEventLine, hb]) _ (by simp [hb, TraceLine.Body.name?]))

theorem unreached_of {lines : List TraceLine} {i : Nat} {l : TraceLine} {id : String} {to : String}
    {rejection : Rejection} (hl : lines[i]? = some l) (hb : l.body = .answer .in id to (.rejected rejection))
    (hk : rejection.kind = .unavailable) : unreached lines to = true := by
  simp only [unreached, List.any_eq_true]
  exact ⟨l, List.mem_of_getElem? hl, by simp [hb, hk]⟩

open Classical in
/--
The line of the peer's run that the scenario's line `i` received: the peer's answer at the same place for a mocked
answer to a request to the peer that reached it, and a line that emits the event for a received event of the peer,
before the peer takes an input that arrives after the line (peerBefore).
-/
noncomputable def sourceA (normal : String → Value → CValue) (service peer : String) (arrivals : List Nat)
    (aLines bLines : List TraceLine) (i : Nat) : Option Place :=
  match aLines[i]? with
  | some l =>
    match l.body with
    | .answer .in _ to _ =>
      if (peerTarget? peer aLines to).isSome ∧ unreached aLines to = false then
        if h : ∃ j, j < peerBefore arrivals bLines i ∧ AnswerAt bLines .out to (answersTo (aLines.take i) .in to).length j
        then some (1, h.choose)
        else none
      else none
    | .event .in _ name payload resultOf =>
      match peerName? peer name with
      | some n =>
        if h : ∃ j b, bLines[j]? = some b ∧ j < peerBefore arrivals bLines i ∧ PeerEmits normal service aLines bLines
            (peerFinal normal service peer arrivals aLines bLines) n payload resultOf l.time b then
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

theorem sourceA_cases {normal : String → Value → CValue} {service peer : String} {arrivals : List Nat}
    {aLines bLines : List TraceLine} {i s j : Nat} (h : sourceA normal service peer arrivals aLines bLines i = some (s, j)) :
    s = 1 ∧ ∃ al, aLines[i]? = some al ∧
      ((∃ id to a, al.body = .answer .in id to a ∧ (peerTarget? peer aLines to).isSome ∧
          unreached aLines to = false ∧ AnswerAt bLines .out to (answersTo (aLines.take i) .in to).length j) ∨
        (∃ id name payload resultOf n bl, al.body = .event .in id name payload resultOf ∧
          peerName? peer name = some n ∧ bLines[j]? = some bl ∧
          PeerEmits normal service aLines bLines (peerFinal normal service peer arrivals aLines bLines) n payload resultOf al.time
            bl)) := by
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
          exact ⟨rfl, al, hi, .inl ⟨id, to, a, hb, hc.1, hc.2, hex.choose_spec.2⟩⟩
        · simp at h
      · simp at h
    · next id name payload resultOf hb =>
      split at h
      · next n hn =>
        split at h
        · next hex =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨bl, hbl, -, he⟩ := hex.choose_spec
          exact ⟨rfl, al, hi, .inr ⟨id, name, payload, resultOf, n, bl, hb, hn, hbl, he⟩⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem sourceA_before {normal : String → Value → CValue} {service peer : String} {arrivals : List Nat}
    {aLines bLines : List TraceLine} {i s j : Nat} (h : sourceA normal service peer arrivals aLines bLines i = some (s, j)) :
    j < peerBefore arrivals bLines i := by
  unfold sourceA at h
  split at h
  · split at h
    · split at h
      · split at h
        · next hex =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact hex.choose_spec.1
        · simp at h
      · simp at h
    · split at h
      · split at h
        · next hex =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          obtain ⟨_, _, hj, _⟩ := hex.choose_spec
          exact hj
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
How the scenario's service `service`, member 0, and its peer `peer`, member 1, see each other's values. The peer
receives a value of a request or event in the form `canon` that its run writes, with each createKey value of the run as
its peer key and each string that a prefix of the final bindings binds as the peer's createKey value bound to it
(peerForward); the scenario's service receives a value of an answer or event that stands for the peer's under the final
bindings (PeerSees).
-/
def peerAgree (normal : String → Value → CValue) (canon : String → Value → Value) (service peer : String)
    (arrivals : List Nat) (aLines bLines : List TraceLine) : Agree
  | 0, 1, n, x, y => ∃ bs, bs <+: peerFinal normal service peer arrivals aLines bLines ∧
    y = canon n ((peerKeys service aLines ++ bs.map fun (p : String × String) => (p.2, p.1)).rename x)
  | 1, 0, m, x, y => ∃ n, peerName? peer m = some n ∧
    PeerSees normal service aLines bLines (peerFinal normal service peer arrivals aLines bLines) n x y
  | _, _, _, _, _ => False

/--
Stage 2 of the check of a scenario's mocks of a peer. Let `aLines` be the scenario's run of the service `service`, and
`bLines` a run of the peer `peer`, whose `in` lines are those that a run writes for the derived inputs (peerInputs),
and which sends no request to `service`: it names a definition of `service` only on a received event. Nothing checks
this, and a peer's run can send such requests; the check neither delivers them nor compares them. The given state and
the elsewhere inputs give the peer no event of `service`. When the check finds no violation, an execution of the two runs on a well formed network
exists: each request of the scenario's run to the peer that reached it arrives at the peer at its send time, each
event of `service` that the peer receives comes from the scenario's run at its emit time, and each mocked answer and
received event of the peer comes from the peer's run, sent at or before the time the scenario receives it and before
the peer receives a line that the scenario sends after it (WellFormed.causal), with the values that the two runs see
(peerAgree).
-/
theorem network_realizes {normal : String → Value → CValue} {canon : String → Value → Value} {service peer : String}
    {received : List String} {state : List Step} {elsewhere : List (Nat × Step)} {aLines bLines : List TraceLine}
    {halted : Option (Origin × String)}
    (hrun : RunOf canon ((peerInputs normal service peer received state elsewhere aLines bLines).map (·.1)) bLines)
    (hstar : ∀ l ∈ bLines, isEventLine l = false → ∀ n, l.body.name? = some n → peerName? service n = none)
    (hown : ∀ s ∈ state ++ elsewhere.map (·.2), ∀ id name x r, s.body = .event id name x r →
      peerName? service name = none)
    (h : peerFindings normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines halted = []) :
    ∃ source, WellFormed (peerAgree normal canon service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines)
      ⟨[(service, aLines), (peer, bLines)], source⟩ := by
  let inputs := peerInputs normal service peer received state elsewhere aLines bLines
  let source : Place → Option Place
    | (0, i) => sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i
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
        (∀ id to a, l.body ≠ .answer .in id to a) ∧
        Carries (peerAgree normal canon service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines) e 0 1 al l := by
    intro j i hs
    obtain ⟨k, st, l, hk, hl⟩ := deliveredAt_spec (sourceB_spec hs).2
    obtain ⟨al, b, hal, hb, rfl⟩ := mem_peerInputs_line (List.mem_of_getElem? hk)
    have hw := hrun.2 k _ _ (by rw [List.getElem?_map, show inputs[k]? = _ from hk]; rfl) hl
    exact ⟨al, l, hal, (mem_inLines (List.mem_of_getElem? hl)).1,
      peerInput_carries hname0 hname1
        (fun _ _ => ⟨_, peerBindings_prefix (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hal).1), rfl⟩) hb hw⟩
  have fromA : ∀ i s j, sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i = some (s, j) → ∃ al bl,
      aLines[i]? = some al ∧ bLines[j]? = some bl ∧ bl.body.dir = .out ∧ al.body.dir = .in ∧
        bl.time.time ≤ al.time.time ∧ Carries (peerAgree normal canon service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines) e 1 0 bl al := by
    intro i s j hs
    obtain ⟨_, al, hal, hc⟩ := sourceA_cases hs
    rcases hc with ⟨id, to, a, hb, ht, hu, bl, id', b, hbl, hbb, hk⟩ |
      ⟨id, name, payload, resultOf, n, bl, hb, hn, hbl, he⟩
    · obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp ht
      obtain ⟨t, b', hb', hsame, hle⟩ := mocked_answer_given h hal hb htarget hu
      have hat := answersTo_at hbl hbb
      rw [hk, answersTo_take_getElem? hb'] at hat
      simp only [Option.some.injEq, Prod.mk.injEq] at hat
      obtain ⟨rfl, rfl⟩ := hat
      refine ⟨al, bl, hal, hbl, by simp [hbb, TraceLine.Body.dir], by simp [hb, TraceLine.Body.dir], hle, ?_⟩
      obtain ⟨m, hm, hmt⟩ := Option.bind_eq_some_iff.mp htarget
      simp only [Carries, hbb, hb, hname1, hlines0]
      exact ⟨trivial, m, hm, by simp [hmt], AnswerCarries.mono (fun _ _ hp => ⟨target, hmt, hp⟩) hsame⟩
    · obtain ⟨id', p, ro, hbb, hr, hle, hp⟩ := he
      refine ⟨al, bl, hal, hbl, by simp [hbb, TraceLine.Body.dir], by simp [hb, TraceLine.Body.dir], hle, ?_⟩
      simp only [Carries, hbb, hb, hname1]
      exact ⟨hn, n, hn, hp⟩
  have hlen : (peerArrivals service peer received state elsewhere aLines).length = (inLines bLines).length := by
    rw [← peerInputs_arrivals (normal := normal) (bLines := bLines), List.length_map, ← hrun.1, List.length_map]
  have inOf : ∀ i s j, sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines
      bLines i = some (s, j) → ∃ al, aLines[i]? = some al ∧ al.body.dir = .in := by
    intro i s j hs
    obtain ⟨-, al, hal, hc⟩ := sourceA_cases hs
    refine ⟨al, hal, ?_⟩
    rcases hc with ⟨_, _, _, hb, -⟩ | ⟨_, _, _, _, _, _, hb, -⟩ <;> simp [hb, TraceLine.Body.dir]
  refine ⟨source, show WellFormed _ e from ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
            obtain ⟨_, _, _, hbb, -⟩ := he
            simp [isEventLine, hbb] at hev
        · rw [hsent] at hbl
          cases hbl
          obtain ⟨_, _, _, hbb, -⟩ := he
          simp [isEventLine, hbb] at hev
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
      obtain ⟨_, l1, -, hl1, -, -, -, hna, -⟩ := fromB _ _ hs
      have hl1' : bLines[i]? = some l := hl
      rw [hl1] at hl1'
      cases hl1'
      exact absurd hb (hna _ _ _)
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)
  · intro r i l id to rejection hl hb hk
    obtain _ | _ | r := r
    · show sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i = none
      cases hs : sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i with
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
        obtain ⟨_, l1, -, hl1, -, -, -, hna, -⟩ := fromB _ _ hs
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
        obtain ⟨hj, hbl⟩ := getElem?_take_some hbl
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hk
        have hex : ∃ j, j < peerBefore (peerArrivals service peer received state elsewhere aLines) bLines i ∧
            AnswerAt bLines .out to (answersTo (aLines.take i) .in to).length j :=
          ⟨j, hj, bl, id', b, hbl, hbb, hk⟩
        refine ⟨hex.choose, ?_⟩
        show sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i = some (1, hex.choose)
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
        have hex := received_event_emitted h hl0 hb hn'
        refine ⟨hex.choose, ?_⟩
        show sourceA normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i = some (1, hex.choose)
        unfold sourceA
        simp only [hl0, hb, hn']
        rw [dite_eq_left hex]
      · omega
    · obtain _ | _ | s := s
      · have hl1 : bLines[i]? = some l := hl
        have hn' : peerName? service name = some n := hn
        obtain ⟨k, hk⟩ := inLines_of hl1 (by simp [hb, TraceLine.Body.dir])
        obtain ⟨⟨st, o⟩, hi⟩ : ∃ x, inputs[k]? = some x := by
          have := (List.getElem?_eq_some_iff.mp hk).1
          rw [← hrun.1, List.length_map] at this
          exact ⟨_, List.getElem?_eq_getElem this⟩
        have hw := hrun.2 k st _ (by rw [List.getElem?_map, hi]; rfl) hk
        obtain ⟨sid, x, r', hst⟩ := writes_event hw hb
        have hnone : ∀ s ∈ state ++ elsewhere.map (·.2), ∀ id x r, s.body ≠ .event id name x r :=
          fun s hs id x r he => by rw [hown s hs id name x r he] at hn'; cases hn'
        cases o with
        | given =>
          exact absurd hst (hnone st (List.mem_append_left _ (mem_peerInputs_given (List.mem_of_getElem? hi))) _ _ _)
        | elsewhere j =>
          obtain ⟨s', hs', keys, hb'⟩ := mem_peerInputs_elsewhere (List.mem_of_getElem? hi)
          rw [hb'] at hst
          obtain ⟨_, _, _, he⟩ := forPeer_event hst
          exact absurd he (hnone s' (List.mem_append_right _ hs') _ _ _)
        | line i' =>
          obtain ⟨j, hj⟩ := deliveredAt_of hi hk
          obtain ⟨k', _, _, hk1, hk2⟩ := deliveredAt_spec hj
          cases peerInputs_line_unique hi hk1
          rw [hk] at hk2
          cases hk2
          exact ⟨i', sourceB_of hj⟩
      · exact absurd rfl hsr
      · omega
    · exact absurd (hl.symm.trans (hline2 r i)) (by simp)
  · intro r s i l hsr hslen hl hsend
    obtain _ | _ | r := r
    · obtain _ | _ | s := s
      · exact absurd rfl hsr
      · have hl0 : aLines[i]? = some l := hl
        have hsend' : (peerBody? peer aLines [] l).isSome := hsend
        rw [← peerBody_isSome (keys := peerForward normal service peer (peerArrivals service peer received state elsewhere aLines) aLines bLines i)] at hsend'
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
      · have hl1 : bLines[i]? = some l := hl
        have hsend' : (peerBody? service bLines [] l).isSome := hsend
        rw [peerBody_none hstar (List.mem_of_getElem? hl1)] at hsend'
        cases hsend'
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
      have hle := arrival_le hlen (Nat.lt_of_le_of_lt hj (sourceA_before hs)) hl (arrivals_of_line hk)
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
      exact Nat.lt_of_lt_of_le (sourceA_before hs') (before_le hlen hl (arrivals_of_line hk) (by omega))
    · exact absurd (hs.symm.trans (hsrc2 r i)) (by simp)

end Tazuna.Thm.Network
