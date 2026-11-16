import Tazuna.Validation.Commands
import Tazuna.Thm.Service.Command
import Tazuna.Thm.Syntax.Structure

namespace Tazuna.Thm.Validation.Commands

open Tazuna.Data Tazuna.Semantics Tazuna.Validation
open Tazuna.Syntax
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
      ∃ r, some r ∈ j.emitsOf (some (st.ref name)) ∧ r.service = st.service ∧ e.event = r.name := by
  intro e he
  obtain ⟨_, decided, _, _, hl, hdec⟩ := accepted_emits_decided records now name raw written groups vs ha
  obtain ⟨e', he', hev⟩ := hdec e he
  have hlist := hl e' he'
  simp only [Service.lists, hj, List.any_eq_true] at hlist
  obtain ⟨_ | r, ho, hname⟩ := hlist
  · simp at hname
  simp only [Option.any_some] at hname
  obtain ⟨d, hd, hs, hm⟩ := Tazuna.Thm.Syntax.Structure.emitsOf_mem j _ r ho
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
  rw [hev, ← beq_iff_eq.mp hname, Ref.traceName, ite_eq_left (by simp [hsv])]

theorem no_index_reasons (s : Structure) :
    Commands.indexReasons s = [] ↔ ∀ d ∈ s.definitions, ∀ r ∈ s.rejectionReasons d.ref, Commands.isArrayIndex r = false := by
  simp [Commands.indexReasons, List.flatMap_eq_nil_iff, List.filter_eq_nil_iff]

end Tazuna.Thm.Validation.Commands
