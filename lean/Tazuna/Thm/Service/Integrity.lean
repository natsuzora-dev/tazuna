import Tazuna.Service.Integrity
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Records
import Tazuna.Thm.Service.Functions

namespace Tazuna.Thm.Service.Integrity

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Records Tazuna.Thm.Service.Functions

variable {st : Service}

theorem duplicated_eq_false_iff (rs : Records) :
    duplicated st rs = false ↔ rs.Pairwise fun a b => clash st a b = false := by
  induction rs with
  | nil => simp [duplicated]
  | cons r rs ih =>
    simp only [duplicated, Bool.or_eq_false_iff, List.any_eq_false, ih, List.pairwise_cons]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun b hb => by simpa using h₁ b hb, h₂⟩,
      fun ⟨h₁, h₂⟩ => ⟨fun b hb => by simpa using h₁ b hb, h₂⟩⟩

theorem keysDistinct_of_not_duplicated {rs : Records} (h : duplicated st rs = false) : KeysDistinct rs := by
  unfold KeysDistinct
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine ((duplicated_eq_false_iff rs).mp h).imp fun {a b} hc he => ?_
  simp only [Prod.mk.injEq] at he
  simp [clash, he.1, he.2] at hc

variable {fs : Functions Id}

theorem mem_danglingRefs (records : Records) (name : String) (row : Row) (f : Fault) :
    f ∈ danglingRefs st records name row ↔
      ∃ field targetEntity v, (row.entity, field, targetEntity) ∈ st.references ∧ row.value.field? field = some v ∧ v ≠ .null ∧
        targetEntity ∈ st.entities ∧ ¬ (∃ x ∈ records, x.entity = targetEntity ∧ x.key = some v.keyString) ∧
        f = match row.key with
          | some key => .danglingRef (st.ref row.entity) key field v.keyString (st.ref name)
          | none => .danglingSingleRef (st.ref row.entity) field v.keyString (st.ref name) := by
  unfold danglingRefs
  simp only [List.mem_filterMap, List.mem_filter, Prod.exists]
  constructor
  · rintro ⟨e, field, targetEntity, ⟨hm, he⟩, hf⟩
    simp only [beq_iff_eq] at he
    subst he
    split at hf
    · cases hf
    · cases hf
    · next v hnn hv =>
      split at hf
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_false, beq_iff_eq,
          not_and] at hc
        simp only [Option.some.injEq] at hf
        exact ⟨field, targetEntity, v, hm, hv, fun h => hnn h, hc.1, fun ⟨x, hx, h1, h2⟩ => hc.2 x hx h1 h2, hf.symm⟩
      · cases hf
  · rintro ⟨field, targetEntity, v, hm, hv, hn, ht, hr, rfl⟩
    refine ⟨row.entity, field, targetEntity, ⟨hm, by simp⟩, ?_⟩
    have hc : (decide (targetEntity ∈ st.entities) &&
        !records.any fun r => r.entity == targetEntity && r.key == some v.keyString) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_false, beq_iff_eq, not_and]
      exact ⟨ht, fun x hx h1 h2 => hr ⟨x, hx, h1, h2⟩⟩
    split
    · next h => rw [hv] at h; cases h
    · next h => rw [hv] at h; cases h; exact absurd rfl hn
    · next w _ h =>
      rw [hv] at h
      cases h
      simp only [hc, ite_true]
      rfl

theorem mem_rowViolations (records : Records) (name : String) (row : Row) (f : Fault) :
    f ∈ (rowViolations st fs records name row).run ↔
      (∃ e, fs.invariant row.entity row.value = .error e ∧ f = issueViolation st (st.ref row.entity) e) ∨
      (∃ c, fs.invariant row.entity row.value = .ok (some c) ∧ f = row.failedInvariant st c (st.ref name)) ∨
        f ∈ danglingRefs st records name row := by
  cases h : fs.invariant row.entity row.value with
  | error e =>
    have : (rowViolations st fs records name row).run =
        issueViolation st (st.ref row.entity) e :: danglingRefs st records name row := by
      simp only [rowViolations, h]; rfl
    rw [this, List.mem_cons]
    constructor
    · rintro (h' | h')
      · exact Or.inl ⟨e, rfl, h'⟩
      · exact Or.inr (Or.inr h')
    · rintro (⟨e', he, h'⟩ | ⟨_, hc, _⟩ | h')
      · cases he; exact Or.inl h'
      · cases hc
      · exact Or.inr h'
  | ok o =>
    cases o with
    | none =>
      have : (rowViolations st fs records name row).run = danglingRefs st records name row := by
        simp only [rowViolations, h]; rfl
      rw [this]
      exact ⟨fun h' => Or.inr (Or.inr h'), fun h' => h'.elim (fun ⟨_, he, _⟩ => by cases he)
        fun h' => h'.elim (fun ⟨_, hc, _⟩ => by cases hc) id⟩
    | some c =>
      have : (rowViolations st fs records name row).run =
          row.failedInvariant st c (st.ref name) :: danglingRefs st records name row := by
        simp only [rowViolations, h]; rfl
      rw [this, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact Or.inr (Or.inl ⟨c, rfl, rfl⟩)
        · exact Or.inr (Or.inr h)
      · rintro (⟨_, he, _⟩ | ⟨c', hc, rfl⟩ | h)
        · cases he
        · cases hc; exact Or.inl rfl
        · exact Or.inr h

theorem mem_integrityViolations (records : Records) (name : String) (f : Fault) :
    f ∈ (integrityViolations st fs records name).run ↔
      (∃ row ∈ records, row.entity ∈ st.entities ∧ f ∈ (rowViolations st fs records name row).run) ∨
        (∃ schema, fs.serviceInvariant records = .error schema ∧ f = .exception (schema.map st.schemaOwner)) ∨
        ∃ c, fs.serviceInvariant records = .ok (some c) ∧ f = .failedServiceInvariant c (st.ref name) := by
  let rows := ((st.entities.flatMap fun e => records.filter (·.entity == e)).map fun x =>
    (rowViolations st fs records name x).run).flatten
  have hrows : f ∈ rows ↔
      ∃ row ∈ records, row.entity ∈ st.entities ∧ f ∈ (rowViolations st fs records name row).run := by
    simp only [rows, List.mem_flatten, List.mem_map, List.mem_flatMap, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨_, ⟨row, ⟨e, he, hr, rfl⟩, rfl⟩, hm⟩
      exact ⟨row, hr, he, hm⟩
    · rintro ⟨row, hr, he, hm⟩
      exact ⟨_, ⟨row, ⟨row.entity, he, hr, rfl⟩, rfl⟩, hm⟩
  cases h : fs.serviceInvariant records with
  | error e =>
    have : (integrityViolations st fs records name).run = rows ++ [.exception (e.map st.schemaOwner)] := by
      simp only [integrityViolations, mapM_id, h]; rfl
    rw [this, List.mem_append, hrows, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨e, rfl, h⟩)
    · rintro (h | ⟨e', he, h⟩ | ⟨_, hc, _⟩)
      · exact Or.inl h
      · cases he; exact Or.inr h
      · cases hc
  | ok o =>
    cases o with
    | none =>
      have : (integrityViolations st fs records name).run = rows := by
        simp only [integrityViolations, mapM_id, h]; rfl
      rw [this, hrows]
      exact ⟨Or.inl, fun h' => h'.elim id fun h' => h'.elim (fun ⟨_, he, _⟩ => by cases he)
        fun ⟨_, hc, _⟩ => by cases hc⟩
    | some c =>
      have : (integrityViolations st fs records name).run =
          rows ++ [.failedServiceInvariant c (st.ref name)] := by
        simp only [integrityViolations, mapM_id, h]; rfl
      rw [this, List.mem_append, hrows, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨c, rfl, rfl⟩)
      · rintro (h | ⟨_, he, _⟩ | ⟨c', hc, rfl⟩)
        · exact Or.inl h
        · cases he
        · cases hc; exact Or.inr rfl

theorem entity_invariant_reported_iff (records : Records) (name : String) (definition : Syntax.Ref) (key c : String)
    (command : Syntax.Ref) :
    .failedEntityInvariant definition key c command ∈ (integrityViolations st fs records name).run ↔
      command = st.ref name ∧ ∃ row ∈ records, definition = st.ref row.entity ∧ row.entity ∈ st.entities ∧
        row.key = some key ∧ fs.invariant row.entity row.value = .ok (some c) := by
  rw [mem_integrityViolations]
  simp only [mem_rowViolations, mem_danglingRefs, Row.failedInvariant]
  constructor
  · rintro (⟨row, hr, he, (⟨_, _, hi⟩ | ⟨c', hi, hk⟩ | ⟨_, _, _, _, _, _, _, _, hk⟩)⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩)
    · exact (not_issue_of_not_halts (fun _ => rfl) rfl hi).elim
    · split at hk
      · rename_i k hkey
        simp only [Fault.failedEntityInvariant.injEq] at hk
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
        exact ⟨rfl, row, hr, rfl, he, hkey, hi⟩
      · cases hk
    · split at hk <;> cases hk
    · cases h
    · cases h
  · rintro ⟨rfl, row, hr, rfl, he, hk, hi⟩
    exact Or.inl ⟨row, hr, he, Or.inr (Or.inl ⟨c, hi, by rw [hk]⟩)⟩

theorem single_invariant_reported_iff (records : Records) (name : String) (definition : Syntax.Ref) (c : String)
    (command : Syntax.Ref) :
    .failedSingleInvariant definition c command ∈ (integrityViolations st fs records name).run ↔
      command = st.ref name ∧ ∃ row ∈ records, definition = st.ref row.entity ∧ row.entity ∈ st.entities ∧
        row.key = none ∧ fs.invariant row.entity row.value = .ok (some c) := by
  rw [mem_integrityViolations]
  simp only [mem_rowViolations, mem_danglingRefs, Row.failedInvariant]
  constructor
  · rintro (⟨row, hr, he, (⟨_, _, hi⟩ | ⟨c', hi, hk⟩ | ⟨_, _, _, _, _, _, _, _, hk⟩)⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩)
    · exact (not_issue_of_not_halts (fun _ => rfl) rfl hi).elim
    · split at hk
      · cases hk
      · rename_i hkey
        simp only [Fault.failedSingleInvariant.injEq] at hk
        obtain ⟨rfl, rfl, rfl⟩ := hk
        exact ⟨rfl, row, hr, rfl, he, hkey, hi⟩
    · split at hk <;> cases hk
    · cases h
    · cases h
  · rintro ⟨rfl, row, hr, rfl, he, hk, hi⟩
    exact Or.inl ⟨row, hr, he, Or.inr (Or.inl ⟨c, hi, by rw [hk]⟩)⟩

theorem service_invariant_reported_iff (records : Records) (name : String) (c : String) (command : Syntax.Ref) :
    .failedServiceInvariant c command ∈ (integrityViolations st fs records name).run ↔
      command = st.ref name ∧ fs.serviceInvariant records = .ok (some c) := by
  rw [mem_integrityViolations]
  simp only [mem_rowViolations, mem_danglingRefs, Row.failedInvariant]
  constructor
  · rintro (⟨row, _, _, (⟨_, _, hi⟩ | ⟨_, _, hk⟩ | ⟨_, _, _, _, _, _, _, _, hk⟩)⟩ | ⟨_, _, h⟩ | ⟨c', hs, hk⟩)
    · exact (not_issue_of_not_halts (fun _ => rfl) rfl hi).elim
    · split at hk <;> cases hk
    · split at hk <;> cases hk
    · cases h
    · simp only [Fault.failedServiceInvariant.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨rfl, hs⟩
  · rintro ⟨rfl, hs⟩
    exact Or.inr (Or.inr ⟨c, hs, rfl⟩)

theorem dangling_ref_reported_iff (records : Records) (name : String) (definition : Syntax.Ref)
    (key field targetKey : String) (command : Syntax.Ref) :
    .danglingRef definition key field targetKey command ∈ (integrityViolations st fs records name).run ↔
      command = st.ref name ∧ ∃ row ∈ records, definition = st.ref row.entity ∧ row.entity ∈ st.entities ∧
        row.key = some key ∧ ∃ targetEntity, (row.entity, field, targetEntity) ∈ st.references ∧
        targetEntity ∈ st.entities ∧ ∃ v, row.value.field? field = some v ∧ v ≠ .null ∧ v.keyString = targetKey ∧
          ¬ ∃ x ∈ records, x.entity = targetEntity ∧ x.key = some targetKey := by
  rw [mem_integrityViolations]
  simp only [mem_rowViolations, mem_danglingRefs, Row.failedInvariant]
  constructor
  · rintro (⟨row, hr, he, (⟨_, _, hi⟩ | ⟨_, _, hk⟩ | ⟨f, t, v, hm, hv, hn, ht, hx, hk⟩)⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩)
    · exact (not_issue_of_not_halts (fun _ => rfl) rfl hi).elim
    · split at hk <;> cases hk
    · split at hk
      · rename_i k hkey
        simp only [Fault.danglingRef.injEq] at hk
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
        exact ⟨rfl, row, hr, rfl, he, hkey, t, hm, ht, v, hv, hn, rfl, hx⟩
      · cases hk
    · cases h
    · cases h
  · rintro ⟨rfl, row, hr, rfl, he, hk, targetEntity, hm, ht, v, hv, hn, rfl, hx⟩
    exact Or.inl ⟨row, hr, he, Or.inr (Or.inr ⟨field, targetEntity, v, hm, hv, hn, ht, hx, by rw [hk]⟩)⟩

theorem dangling_single_ref_reported_iff (records : Records) (name : String) (definition : Syntax.Ref)
    (field targetKey : String) (command : Syntax.Ref) :
    .danglingSingleRef definition field targetKey command ∈ (integrityViolations st fs records name).run ↔
      command = st.ref name ∧ ∃ row ∈ records, definition = st.ref row.entity ∧ row.entity ∈ st.entities ∧
        row.key = none ∧ ∃ targetEntity, (row.entity, field, targetEntity) ∈ st.references ∧
        targetEntity ∈ st.entities ∧ ∃ v, row.value.field? field = some v ∧ v ≠ .null ∧ v.keyString = targetKey ∧
          ¬ ∃ x ∈ records, x.entity = targetEntity ∧ x.key = some targetKey := by
  rw [mem_integrityViolations]
  simp only [mem_rowViolations, mem_danglingRefs, Row.failedInvariant]
  constructor
  · rintro (⟨row, hr, he, (⟨_, _, hi⟩ | ⟨_, _, hk⟩ | ⟨f, t, v, hm, hv, hn, ht, hx, hk⟩)⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩)
    · exact (not_issue_of_not_halts (fun _ => rfl) rfl hi).elim
    · split at hk <;> cases hk
    · split at hk
      · cases hk
      · rename_i hkey
        simp only [Fault.danglingSingleRef.injEq] at hk
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
        exact ⟨rfl, row, hr, rfl, he, hkey, t, hm, ht, v, hv, hn, rfl, hx⟩
    · cases h
    · cases h
  · rintro ⟨rfl, row, hr, rfl, he, hk, targetEntity, hm, ht, v, hv, hn, rfl, hx⟩
    exact Or.inl ⟨row, hr, he, Or.inr (Or.inr ⟨field, targetEntity, v, hm, hv, hn, ht, hx, by rw [hk]⟩)⟩

end Tazuna.Thm.Service.Integrity
