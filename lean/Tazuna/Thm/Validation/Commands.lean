import Tazuna.Validation.Commands
import Tazuna.Thm.Service.Command
import Tazuna.Thm.Spec.Structure

namespace Tazuna.Thm.Validation.Commands

open Tazuna.Data Tazuna.Service Tazuna.Validation
open Tazuna.Spec
open Tazuna.Thm.Service.Command

theorem commands_emit_own_events (s : Structure) :
    Commands.foreignEvents s = [] ↔
      ∀ d ∈ s.definitions, ∀ c, d.body = .command c → ∀ e ∈ c.emits, e.service = d.service := by
  simp only [Commands.foreignEvents, List.flatMap_eq_nil_iff]
  constructor
  · intro h d hd c hb e he
    have hd' := h d hd
    rw [hb] at hd'
    have := List.filterMap_eq_nil_iff.mp hd' e he
    exact Classical.byContradiction fun hne => by simp [hne] at this
  · intro h d hd
    cases hb : d.body with
    | command c =>
      refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
      simp [h d hd c hb e he]
    | _ => rfl

theorem accepted_command_emits_own_events (j : Structure) (h : Commands.foreignEvents j = []) (st : Service)
    (hj : st.«structure» = j) (fs : Functions Id) (records : Records) (now : Time) (name : String) (raw : Value)
    (written : Records) (groups : List (List Emit)) (vs : List Fault)
    (ha : evaluate st fs records now name raw = .accepted written groups vs) :
    ∀ e ∈ groups.flatten,
      ∃ r, r ∈ j.emitsOf (st.ref name) ∧ r.service = st.service ∧ e.event = r := by
  intro e he
  obtain ⟨_, decided, _, _, hl, rfl⟩ := accepted_emits_decided records now name raw written groups vs ha
  have hs := mem_orderedGroups _ _ e he
  rw [decide_payloads_sorted] at hs
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp hs
  have hlist := hl e' he'
  simp only [Service.lists, hj, List.contains_iff_mem] at hlist
  obtain ⟨d, hd, hs, hm⟩ := Tazuna.Thm.Spec.Structure.emitsOf_mem j _ _ hlist
  have hsv : e'.event.service = st.service := by
    cases hb : d.body with
    | command c =>
      simp only [hb] at hm
      rw [(commands_emit_own_events j).mp h d hd c hb _ hm, show d.service = (st.ref name).service from
        congrArg Ref.service hs]
      rfl
    | _ => simp [hb] at hm
  exact ⟨e'.event, hlist, hsv, rfl⟩

end Tazuna.Thm.Validation.Commands
