import Tazuna.Semantics.System.Peer

namespace Tazuna.Thm.Semantics.System.Peer

open Tazuna.Data Tazuna.Semantics

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

theorem peerName_traceName (p n : String) : peerName? p s!"{p}.{n}" = some n := by
  simp only [peerName?, toString]
  simp
  apply String.toList_inj.mp
  simp [String.toList_append, ← String.length_toList]

theorem unavailable_mapOutput {f : Value → Value} : ∀ a : Answer, (a.mapOutput f).unavailable = a.unavailable
  | .accepted _ | .fulfilled _ | .rejected _ => rfl

theorem mapOutput_mapOutput {f g : Value → Value} : ∀ a : Answer, (a.mapOutput f).mapOutput g = a.mapOutput (g ∘ f)
  | .accepted none | .accepted (some _) | .fulfilled _ | .rejected _ => rfl

theorem forPeer_received {b : Step.Body} {keys : Bindings} : (b.forPeer keys).received? = b.received? := by
  cases b <;> rfl

theorem inLines_of {lines : List TraceLine} {i : Nat} {l : TraceLine} (hl : lines[i]? = some l)
    (hd : l.body.dir = .in) : ∃ k : Nat, (inLines lines)[k]? = some (l, i) := by
  have hm : (l, i) ∈ inLines lines := by
    simp only [inLines, List.mem_filter, beq_iff_eq]
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hl, hd⟩
  exact List.mem_iff_getElem?.mp hm

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

end Tazuna.Thm.Semantics.System.Peer
