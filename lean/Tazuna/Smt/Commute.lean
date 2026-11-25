import Tazuna.Smt.Checked
import Tazuna.Semantics.StepRename

/-! T5 for a checked spec. Every service of a spec that passed check respects every renaming of the ids steps make
(`CheckedSpec.equivariant`): the spec is what a closed program evaluates to, and evaluation relates a closed program's
value to itself under every renaming (`Expr.eval_rel`), which for structure values says that the functions and
values they keep relate to themselves. -/

namespace Tazuna.Smt

open Tazuna.Ir

mutual
theorem comparable_of_plain : (t : Ty) → t.plain = true → t.comparable = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .tuple ts, h => comparables_of_plains ts h
  | .adt _ _ vs, h => comparabless_of_plainss vs h
  | .list _, h | .bag _, h | .table .., h | .fn .., h | .param _, h | .dsl .., h => by simp [Ty.plain] at h
theorem comparables_of_plains : (ts : List Ty) → Ty.plains ts = true → Ty.comparables ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.plains, Bool.and_eq_true] at h
    simp [Ty.comparables, comparable_of_plain t h.1, comparables_of_plains ts h.2]
theorem comparabless_of_plainss : (vs : List (List Ty)) → Ty.plainss vs = true → Ty.comparabless vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.plainss, Bool.and_eq_true] at h
    simp [Ty.comparabless, comparables_of_plains ts h.1, comparabless_of_plainss vs h.2]
end

mutual
theorem comparable_of_embeddable : (t : Ty) → t.embeddable = true → t.comparable = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .dsl k _, h => h
  | .adt 0 _ vs, h => by
    simp only [Ty.embeddable, Option.isSome_iff_exists] at h
    obtain ⟨⟨rfl⟩, _⟩ := h
    rfl
  | .adt (_ + 1) _ vs, h => comparabless_of_embeddabless vs h
  | .tuple ts, h => comparables_of_embeddables ts h
  | .list t, h | .bag t, h => comparable_of_embeddable t h
  | .table k v, h => by
    simp only [Ty.embeddable, Bool.and_eq_true] at h
    simp [Ty.comparable, comparable_of_embeddable k h.1, comparable_of_embeddable v h.2]
  | .fn _ _, h | .param _, h => by simp [Ty.embeddable] at h
theorem comparables_of_embeddables : (ts : List Ty) → Ty.embeddables ts = true → Ty.comparables ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.embeddables, Bool.and_eq_true] at h
    simp [Ty.comparables, comparable_of_embeddable t h.1, comparables_of_embeddables ts h.2]
theorem comparabless_of_embeddabless : (vs : List (List Ty)) → Ty.embeddabless vs = true → Ty.comparabless vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at h
    simp [Ty.comparabless, comparables_of_embeddables ts h.1, comparabless_of_embeddabless vs h.2]
end

/-- Every service of a checked spec respects every renaming of the ids steps make: its functions and the values they
captured relate to themselves under every renaming, and its caller and key types are comparable. -/
theorem CheckedSpec.equivariant (c : CheckedSpec) : ∀ v ∈ c.spec.services, v.Equivariant := by
  intro v hv
  have hk := c.checked v hv
  refine ⟨?_, fun m hm => comparable_of_plain _ (Ty.plain_of_orderable _ (hk.keys m hm).1), fun R => ?_⟩
  · have h := hk.stateTys
    simp only [ServiceV.stateTys, Bool.and_eq_true] at h
    exact comparable_of_embeddable _ h.2.1
  · exact Var.get_rel c.program.root (Defs.eval_rel (R := R) c.program.defs) () () trivial rfl v hv

end Tazuna.Smt
