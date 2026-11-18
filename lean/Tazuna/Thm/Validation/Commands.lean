import Tazuna.Validation.Commands
import Tazuna.Thm.Service.Command
import Tazuna.Thm.Spec.Structure

namespace Tazuna.Thm.Validation.Commands

open Tazuna.Data Tazuna.Service Tazuna.Validation
open Tazuna.Spec
open Tazuna.Thm.Service.Command

theorem commands_emit_own_events (s : Structure) :
    Commands.foreignEvents s = [] ↔
      ∀ d ∈ s.definitions, ∀ rejects input output emits references binds requires,
        d.body = .command rejects input output emits references binds requires →
          ∀ e, some e ∈ emits → e.service = d.service := by
  simp only [Commands.foreignEvents, List.flatMap_eq_nil_iff]
  constructor
  · intro h d hd rejects input output emits references binds requires hb e he
    have hd' := h d hd
    rw [hb] at hd'
    have := List.filterMap_eq_nil_iff.mp hd' (some e) he
    exact Classical.byContradiction fun hne => by simp [hne] at this
  · intro h d hd
    cases hb : d.body with
    | command rejects input output emits references binds requires =>
      refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
      cases e with
      | none => rfl
      | some e => simp [h d hd rejects input output emits references binds requires hb e he]
    | _ => rfl

theorem accepted_command_emits_own_events (j : Structure) (h : Commands.foreignEvents j = []) (st : Service)
    (hj : st.«structure» = j) (fs : Functions Id) (records : Records) (now : Time) (name : String) (raw : Value)
    (written : Records) (groups : List (List Emit)) (vs : List Fault)
    (ha : evaluate st fs records now name raw = .accepted written groups vs) :
    ∀ e ∈ groups.flatten,
      ∃ r, some r ∈ j.emitsOf (some (st.ref name)) ∧ r.service = st.service ∧ e.event = r := by
  intro e he
  obtain ⟨_, decided, _, _, hl, out, -, hlen, hz, rfl⟩ := accepted_emits_decided records now name raw written groups vs ha
  obtain ⟨e', hx⟩ := Tazuna.Thm.Data.Basic.exists_zip_of_mem_right hlen (mem_orderedGroups _ _ e he)
  have he' := (List.of_mem_zip hx).1
  have hev := (hz _ hx).1
  have hlist := hl e' he'
  simp only [Service.lists, hj, List.any_eq_true] at hlist
  obtain ⟨_ | r, ho, hname⟩ := hlist
  · simp at hname
  have hname : r = e'.event := by simpa using hname
  obtain ⟨d, hd, hs, hm⟩ := Tazuna.Thm.Spec.Structure.emitsOf_mem j _ r ho
  have hsv : r.service = st.service := by
    cases hb : d.body with
    | command rejects input output emits references binds requires =>
      simp only [hb] at hm
      have := (commands_emit_own_events j).mp h d hd rejects input output emits references binds requires hb r hm
      simp only [sameRef, beq_iff_eq] at hs
      rw [this, show d.service = (st.ref name).service from congrArg Ref.service hs]
      rfl
    | _ => simp [hb] at hm
  refine ⟨r, ho, hsv, ?_⟩
  rw [hev, hname]

end Tazuna.Thm.Validation.Commands
