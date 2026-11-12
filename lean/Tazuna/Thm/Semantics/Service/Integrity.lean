import Tazuna.Semantics.Service.Integrity
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Semantics.Service.Records
import Tazuna.Thm.Semantics.Functions

namespace Tazuna.Thm.Semantics.Service.Integrity

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.Functions

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

theorem uniqueChecked_congr {u : List String} {a b : Value} (h : uniqueValues u a = uniqueValues u b) :
    uniqueChecked u a = uniqueChecked u b := by
  have hf : ∀ f ∈ u, a.field? f = b.field? f := List.map_inj_left.mp h
  unfold uniqueChecked
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun hh f hm => by rw [← hf f hm]; exact hh f hm, fun hh f hm => by rw [hf f hm]; exact hh f hm⟩

theorem clash_comm (a b : Row) : clash st a b = clash st b a := by
  have hk : (a.key == b.key) = (b.key == a.key) := by
    by_cases h : a.key = b.key
    · simp [h]
    · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr fun e => h e.symm]
  unfold clash
  by_cases he : a.entity = b.entity
  · rw [he, hk]
    by_cases hu : uniqueValues (st.uniqueOf b.entity) a.value = uniqueValues (st.uniqueOf b.entity) b.value
    · rw [uniqueChecked_congr hu, hu, beq_self_eq_true]
    · have h₁ : (uniqueValues (st.uniqueOf b.entity) a.value == uniqueValues (st.uniqueOf b.entity) b.value) = false :=
        beq_eq_false_iff_ne.mpr hu
      have h₂ : (uniqueValues (st.uniqueOf b.entity) b.value == uniqueValues (st.uniqueOf b.entity) a.value) = false :=
        beq_eq_false_iff_ne.mpr fun e => hu e.symm
      simp only [h₁, h₂, Bool.and_false]
  · rw [beq_eq_false_iff_ne.mpr he, beq_eq_false_iff_ne.mpr fun e => he e.symm, Bool.false_and, Bool.false_and]

theorem duplicated_perm {l l' : Records} (h : l.Perm l') : duplicated st l = duplicated st l' := by
  have hp : l.Pairwise (fun a b => clash st a b = false) ↔ l'.Pairwise (fun a b => clash st a b = false) :=
    h.pairwise_iff fun {a b} hab => by rw [clash_comm]; exact hab
  cases h₁ : duplicated st l <;> cases h₂ : duplicated st l'
  · rfl
  · exact absurd ((duplicated_eq_false_iff l').mpr (hp.mp ((duplicated_eq_false_iff l).mp h₁))) (by simp [h₂])
  · exact absurd ((duplicated_eq_false_iff l).mpr (hp.mpr ((duplicated_eq_false_iff l').mp h₂))) (by simp [h₁])
  · rfl

theorem duplicated_append {xs ys : Records} (hx : duplicated st xs = false) :
    duplicated st (xs ++ ys) = true ↔ duplicated st ys = true ∨ ∃ w ∈ ys, ∃ b ∈ xs, clash st w b = true := by
  have hpx := (duplicated_eq_false_iff xs).mp hx
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Bool.not_eq_true, not_exists, not_and] at hn
    have : duplicated st (xs ++ ys) = false := by
      rw [duplicated_eq_false_iff, List.pairwise_append]
      exact ⟨hpx, (duplicated_eq_false_iff ys).mp hn.1, fun a ha b hb => by
        rw [clash_comm]; simpa using hn.2 b hb a ha⟩
    simp [h] at this
  · intro h
    cases hd : duplicated st (xs ++ ys)
    · rw [duplicated_eq_false_iff, List.pairwise_append] at hd
      rcases h with h | ⟨w, hw, b, hb, hc⟩
      · simp [(duplicated_eq_false_iff ys).mpr hd.2.1] at h
      · have := hd.2.2 b hb w hw
        rw [clash_comm] at this
        simp [this] at hc
    · rfl

theorem map_perm_filter (f : Row → Row) (l : List Row) :
    (l.map f).Perm (l.filter (fun r => f r == r) ++ (l.filter fun r => !(f r == r)).map f) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    by_cases hx : f x = x
    · simp only [List.map_cons, List.filter_cons, hx, beq_self_eq_true, ↓reduceIte, Bool.not_true,
        Bool.false_eq_true, List.cons_append]
      exact ih.cons x
    · have hb : (f x == x) = false := by simpa using hx
      simp only [List.map_cons, List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        List.map_cons]
      exact (ih.cons (f x)).trans List.perm_middle.symm

theorem filter_true (l : Records) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr fun _ _ => rfl

theorem map_shape (g : Row → Row) (rs : Records) :
    ∃ (f : Row → Row) (p : Row → Bool) (tail : Records), rs.map g = (rs.map f).filter p ++ tail :=
  ⟨g, fun _ => true, [], by rw [filter_true, List.append_nil]⟩

theorem append_shape (rs tail : Records) :
    ∃ (f : Row → Row) (p : Row → Bool) (tail' : Records), rs ++ tail = (rs.map f).filter p ++ tail' :=
  ⟨id, fun _ => true, tail, by rw [List.map_id, filter_true]⟩

theorem filter_shape (q : Row → Bool) (rs : Records) :
    ∃ (f : Row → Row) (p : Row → Bool) (tail : Records), rs.filter q = (rs.map f).filter p ++ tail :=
  ⟨id, q, [], by rw [List.map_id, List.append_nil]⟩

theorem applyEmit_shape (rs : Records) (e : Emit) :
    ∃ (f : Row → Row) (p : Row → Bool) (tail : Records), applyEmit st rs e = (rs.map f).filter p ++ tail := by
  cases hl : st.events.lookup e.event with
  | none => exact ⟨id, fun _ => true, [], by simp [applyEmit, evolve, hl, filter_true]⟩
  | some c =>
    cases c with
    | none => exact ⟨id, fun _ => true, [], by simp [applyEmit, evolve, hl, filter_true]⟩
    | create entity keyField _ =>
      simp only [applyEmit, evolve, hl]
      exact append_shape rs _
    | update entity keyField _ =>
      simp only [applyEmit, evolve, hl]
      split
      · exact map_shape _ rs
      · exact append_shape rs _
    | delete entity keyField _ =>
      simp only [applyEmit, evolve, hl]
      exact filter_shape _ rs
    | set entity _ =>
      simp only [applyEmit, evolve, hl]
      split
      · exact map_shape _ rs
      · exact append_shape rs _

theorem applyAll_kept_written (records : Records) (es : List Emit) :
    ∃ kept written, kept.Sublist records ∧ (applyAll st records es).Perm (kept ++ written) := by
  unfold applyAll
  suffices ∀ (rs kept written : Records), kept.Sublist records → rs.Perm (kept ++ written) →
      ∃ kept' written', kept'.Sublist records ∧ (es.foldl (applyEmit st) rs).Perm (kept' ++ written') from
    this records records [] (List.Sublist.refl _) (by simp)
  induction es with
  | nil => intro rs kept written hk hp; exact ⟨kept, written, hk, hp⟩
  | cons e es ih =>
    intro rs kept written hk hp
    obtain ⟨f, p, tail, he⟩ := applyEmit_shape (st := st) rs e
    rw [List.foldl_cons]
    refine ih _ ((kept.filter fun r => f r == r).filter p)
      (((kept.filter fun r => !(f r == r)).map f).filter p ++ (written.map f).filter p ++ tail)
      ((List.filter_sublist).trans ((List.filter_sublist).trans hk)) ?_
    rw [he]
    refine (((hp.map f).filter p).append_right tail).trans ?_
    rw [List.map_append, List.filter_append]
    refine ((((map_perm_filter f kept).filter p).append_right _).append_right tail).trans ?_
    rw [List.filter_append]
    simp only [List.append_assoc]
    exact List.Perm.refl _

/-- The theorem justifies checking only the records that a command wrote, and deciding unique reads from them. -/
theorem duplicated_applyAll_iff_written_clashes (records : Records) (es : List Emit)
    (h : duplicated st records = false) :
    ∃ kept written, kept.Sublist records ∧ (applyAll st records es).Perm (kept ++ written) ∧
      (duplicated st (applyAll st records es) = true ↔
        duplicated st written = true ∨ ∃ w ∈ written, ∃ b ∈ kept, clash st w b = true) := by
  obtain ⟨kept, written, hk, hp⟩ := applyAll_kept_written (st := st) records es
  have hkd : duplicated st kept = false :=
    (duplicated_eq_false_iff kept).mpr (((duplicated_eq_false_iff records).mp h).sublist hk)
  refine ⟨kept, written, hk, hp, ?_⟩
  rw [duplicated_perm hp]
  exact duplicated_append hkd

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

end Tazuna.Thm.Semantics.Service.Integrity
