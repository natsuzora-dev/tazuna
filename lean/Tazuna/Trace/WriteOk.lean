import Tazuna.Trace.WireThm
import Tazuna.Trace.Run
import Tazuna.Smt.Checked
import Tazuna.Semantics.GenTarget

/-! Writing never fails where check's facts hold: a value of a type that `encodes` has a wire form once every id it holds
has a name (`enc_isSome`), every type a run writes is one of the service's wire types, whose values check found to
encode, and the writer names every id, since its names avoid every outside name the run writes. So a run that faults
nowhere writes a trace (`traceOf_ok`). -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

theorem mapM_isSome {α β : Type} {f : α → Option β} : (xs : List α) → (∀ x ∈ xs, (f x).isSome) →
    (xs.mapM f).isSome
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.1 (mapM_isSome xs fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp [List.mapM_cons, hy, hys]

section
variable (T : List TypeDecl) (name : IdV → Option String)

theorem encs_length : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (ws : List Wire) →
    encs T name ts x = some ws → ws.length = ts.length
  | [], (), ws, h => by simp only [encs, Option.some.injEq] at h; subst h; rfl
  | t :: ts, (y, ys), ws, h => by
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, -, ws', hws', rfl⟩ := h
    simp only [List.length_cons, encs_length ts ys ws' hws']

-- One mutual block proves the theorems together.
set_option linter.unusedSectionVars false

mutual
theorem enc_isSome : (t : Ty) → t.encodes T = true → (x : t.den0) → (∀ i ∈ idsOf T t x, (name i).isSome) →
    (enc T name t x).isSome
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ => rfl
  | .id, _, x, h => by simpa [enc] using h x (List.mem_singleton_self x)
  | .list t, he, xs, h => by
    simp only [enc, Option.isSome_map]
    exact mapM_isSome xs fun x hx => enc_isSome t he x fun i hi => h i (List.mem_flatMap.2 ⟨x, hx, hi⟩)
  | .bag t, he, xs, h => by
    simp only [enc, Option.isSome_map]
    exact mapM_isSome _ fun x hx => enc_isSome t he x fun i hi => h i (List.mem_flatMap.2 ⟨x, hx, hi⟩)
  | .tuple ts, he, x, h => by
    simp only [enc, Option.isSome_map]
    exact encs_isSome ts he x h
  | .adt 0 _ vs, he, x, _ => by
    simp only [Ty.encodes] at he
    split at he
    · match x with
      | .inl () => rfl
      | .inr (.inl ()) => rfl
    · cases he
  | .adt 1 _ vs, he, x, _ => by
    simp only [Ty.encodes] at he
    split at he
    · match x with
      | .inl () => rfl
    · cases he
  | .adt (i + 2) _ vs, he, x, h => by
    simp only [Ty.encodes] at he
    exact encAlts_isSome vs _ 0 he x h
  | .table k v, he, x, h => by
    simp only [Ty.encodes, Bool.and_eq_true] at he
    simp only [enc, Option.isSome_map]
    refine mapM_isSome _ fun e he' => ?_
    have hk := enc_isSome k he.1 e.1 fun i hi => h i (List.mem_flatMap.2 ⟨e, he', List.mem_append_left _ hi⟩)
    have hv := enc_isSome v he.2 e.2 fun i hi => h i (List.mem_flatMap.2 ⟨e, he', List.mem_append_right _ hi⟩)
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hv
    simp [ha, hb]
  | .fn .., he, _, _ | .param _, he, _, _ | .dsl .., he, _, _ => by simp [Ty.encodes] at he
theorem encs_isSome : (ts : List Ty) → Ty.encodess T ts = true → (x : (Ty.semsWith Dsl.base ts).1) →
    (∀ i ∈ idsOfs T ts x, (name i).isSome) → (encs T name ts x).isSome
  | [], _, (), _ => rfl
  | t :: ts, he, (x, xs), h => by
    simp only [Ty.encodess, Bool.and_eq_true] at he
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
      (enc_isSome t he.1 x fun i hi => h i (List.mem_append_left _ hi))
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.1
      (encs_isSome ts he.2 xs fun i hi => h i (List.mem_append_right _ hi))
    simp [encs, hw, hws]
theorem encAlts_isSome : (vs : List (List Ty)) → (decl : List Variant) → (k : Nat) →
    Ty.encodesAlts T decl k vs = true → (x : (Ty.semAltsWith Dsl.base vs).1) → (∀ i ∈ idsOfAlts T vs x, (name i).isSome) →
    (encAlts T name decl k vs x).isSome
  | [], _, _, _, x, _ => nomatch x
  | fs :: _, decl, k, he, .inl x, h => by
    simp only [Ty.encodesAlts, Bool.and_eq_true] at he
    obtain ⟨⟨hv, hfs⟩, -⟩ := he
    split at hv
    · rename_i var hvar
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.1 (encs_isSome fs hfs x h)
      have hlen := encs_length T name fs x ws hws
      simp [encAlts, hvar, hws, hv.1, hv.2, hlen]
    · cases hv
  | _ :: vs, decl, k, he, .inr y, h => by
    simp only [Ty.encodesAlts, Bool.and_eq_true] at he
    exact encAlts_isSome vs decl (k + 1) he.2 y h
end

end

section
variable {T : List TypeDecl} {v : ServiceV}

/-- Every outside id among `ids` has its name in `A`. -/
def Covers (A : List String) (ids : List IdV) : Prop := ∀ s, IdV.named s ∈ ids → A.contains s = true

/-- What writing one item keeps: names that avoid `A` and keep `Names.Ok`, and a line. -/
def Keeps {α : Type} (A : List String) (f : Names → α → Names × Option Line) (a : α) : Prop :=
  ∀ ns : Names, ns.Ok → ns.avoid = A → (f ns a).1.Ok ∧ (f ns a).1.avoid = A ∧ (f ns a).2.isSome

theorem Names.enc_ok {ns : Names} (h : ns.Ok) {t : Ty} (he : t.encodes T = true) (x : t.den0)
    (hx : Covers ns.avoid (idsOf T t x)) :
    (ns.enc T t x).1.Ok ∧ (ns.enc T t x).1.avoid = ns.avoid ∧ (ns.enc T t x).2.isSome := by
  obtain ⟨h1, h2, -, h4⟩ := Names.bind_ok h (idsOf T t x) hx
  exact ⟨h1, h2, enc_isSome T _ t he x h4⟩

theorem Names.wire_ok {ns : Names} (h : ns.Ok) (n : Nat) : (ns.wire n).1.Ok ∧ (ns.wire n).1.avoid = ns.avoid := by
  unfold Names.wire
  split
  · exact ⟨h, rfl⟩
  · exact ⟨⟨h.avoided, h.named, h.nodup⟩, rfl⟩

theorem writeAll_ok {α : Type} {A : List String} {f : Names → α → Names × Option Line} :
    (as : List α) → (∀ a ∈ as, Keeps A f a) → ∀ ns : Names, ns.Ok → ns.avoid = A →
      (writeAll f ns as).1.Ok ∧ (writeAll f ns as).1.avoid = A ∧ (writeAll f ns as).2.isSome
  | [], _, _, h, ha => ⟨h, ha, rfl⟩
  | a :: as, hk, ns, h, ha => by
    obtain ⟨h1, h2, h3⟩ := hk a List.mem_cons_self ns h ha
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h3
    have ih := writeAll_ok as (fun b hb => hk b (List.mem_cons_of_mem _ hb)) _ h1 h2
    simp only [writeAll]
    revert h1 h2 hl ih
    generalize f ns a = r
    obtain ⟨ns', l'⟩ := r
    intro h1 h2 hl ih
    simp only at hl
    subst hl
    exact ⟨ih.1, ih.2.1, by simp [Option.isSome_map, ih.2.2]⟩

theorem wire_encodes {P : List AnySite} {E : List AnyEffectSite} (chk : Smt.Checked P E T v) {t : Ty}
    (ht : t ∈ v.wireTys) : t.encodes T = true := by
  have h := chk.wire
  simp only [ServiceV.wireOk, List.all_eq_true, Bool.and_eq_true] at h
  exact (h t ht).1.1

theorem pendingOf_mem {e : Ty} : (shs : List (PendingShape e)) → (id : Nat) → (x : Ty.alts (shs.map PendingShape.fields)) →
    ∃ sh ∈ shs, ∃ y, pendingOf shs id x = sh.pending id y
  | sh :: _, _, .inl x => ⟨sh, List.mem_cons_self, x, rfl⟩
  | _ :: shs, id, .inr y => by
    obtain ⟨sh, hsh, z, hz⟩ := pendingOf_mem shs id y
    exact ⟨sh, List.mem_cons_of_mem _ hsh, z, hz⟩

/-- A request a state can hold asks with types the service may request, which are wire types. -/
theorem atShapes_tys {p : Step.Pending v.event} (h : AtShapes (shapes v) p) :
    p.request.input ∈ v.wireTys ∧ p.request.output ∈ v.wireTys ∧ ∀ j, p.request.rejection = some j → j ∈ v.wireTys := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨sh, hsh, y, hy⟩ := pendingOf_mem _ _ x
  rw [hx] at hy
  rw [hy]
  simp only [PendingShape.pending]
  simp only [shapes, List.mem_flatMap] at hsh
  obtain ⟨⟨ks, snd, sites⟩, -, hsh⟩ := hsh
  split at hsh
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hsh
    simp only [requestShapes, requestShapesAt, List.mem_flatMap] at hr
    obtain ⟨⟨o, d⟩, hd, hr⟩ := hr
    have hdecl : ∀ t ∈ (match d with
        | .externalCommand _ i o j => [i, o, j]
        | .externalQuery _ i o _ => [i, o]
        | _ => []), t ∈ v.wireTys := fun t ht => by
      simp only [ServiceV.wireTys]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨(o, d), hd, ht⟩)))
    cases d with
    | externalCommand n i o' j =>
      simp only [List.mem_filterMap] at hr
      obtain ⟨⟨aΓ, a⟩, -, hr⟩ := hr
      split at hr
      · cases hr
        refine ⟨hdecl i (by simp), hdecl o' (by simp), fun j' hj => ?_⟩
        cases hj
        exact hdecl j (by simp)
      · cases hr
    | externalQuery n i o' f =>
      dsimp only at hr
      obtain ⟨_, -, hr⟩ := List.mem_flatMap.1 hr
      obtain ⟨⟨aΓ, a⟩, -, hr⟩ := List.mem_filterMap.1 hr
      split at hr
      · cases hr
        exact ⟨hdecl i (by simp), hdecl o' (by simp), fun j' hj => nomatch hj⟩
      · cases hr
    | command | query | source => simp at hr
  · simp at hsh

end

section
variable (T : List TypeDecl) {v : ServiceV}

theorem finish_answers {s0 : State v} {r : Except Fault (Acc v)} {w : WireVal} :
    (finish T s0 r .accepted).outcome ≠ .answered w ∧ (finish T s0 r .accepted).outcome ≠ .rejected w := by
  rcases finish_outcome (T := T) s0 r .accepted with h | ⟨f, h⟩ <;> rw [h] <;> exact ⟨nofun, nofun⟩

/-- A step answers with a query's output and rejects with a command's rejection, which are wire types. -/
theorem step_outcome_tys (s : State v) (x : Input v) :
    (∀ w, (step T v s x).outcome = .answered w → w.1 ∈ v.wireTys) ∧
      (∀ w, (step T v s x).outcome = .rejected w → w.1 ∈ v.wireTys) := by
  have hc : ∀ i : Fin v.commands.length, (v.commands.get i).rejection ∈ v.wireTys := fun i => by
    simp only [ServiceV.wireTys]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨_, List.get_mem _ _,
        List.mem_cons_of_mem _ List.mem_cons_self⟩)))))
  have hq : ∀ i : Fin v.queries.length, (v.queries.get i).output ∈ v.wireTys := fun i => by
    simp only [ServiceV.wireTys]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, List.get_mem _ _,
        List.mem_cons_of_mem _ List.mem_cons_self⟩)))))
  cases x with
  | command i caller input =>
    simp only [step]
    split
    · exact ⟨nofun, nofun⟩
    · exact ⟨nofun, fun w h => by cases h; exact hc i⟩
    · exact ⟨nofun, nofun⟩
    · exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩
  | query i caller input =>
    simp only [step]
    split
    · exact ⟨nofun, nofun⟩
    · exact ⟨fun w h => by cases h; exact hq i, nofun⟩
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step]
    split
    · exact ⟨nofun, nofun⟩
    · split
      · exact ⟨nofun, nofun⟩
      · split
        · exact ⟨nofun, nofun⟩
        · exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩
  | event i value => exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩
  | clock t =>
    simp only [step]
    split
    · exact ⟨nofun, nofun⟩
    · split
      · exact ⟨nofun, nofun⟩
      · exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩

end

section
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

theorem covers_append {A : List String} {l l' : List IdV} (h : Covers A (l ++ l')) : Covers A l ∧ Covers A l' :=
  ⟨fun s hs => h s (List.mem_append_left _ hs), fun s hs => h s (List.mem_append_right _ hs)⟩

theorem covers_flatMap {α : Type} {A : List String} {f : α → List IdV} {l : List α} (h : Covers A (l.flatMap f)) :
    ∀ a ∈ l, Covers A (f a) := fun a ha s hs => h s (List.mem_flatMap.2 ⟨a, ha, hs⟩)

/-- The out lines of a result that faults nowhere, whose values are of wire types and whose outside ids the names
avoid, are written. -/
theorem outLines_ok (chk : Smt.Checked P E T v) {ns : Names} (h : ns.Ok) (answerTo : Option String) (r : Result v)
    (hnf : ∀ f, r.outcome ≠ .fault f) (hans : ∀ w, r.outcome = .answered w → w.1 ∈ v.wireTys)
    (hrej : ∀ w, r.outcome = .rejected w → w.1 ∈ v.wireTys) (hout : ∀ o ∈ r.out, o.input.1 ∈ v.wireTys)
    (hcov : Covers ns.avoid (r.shownIds T)) :
    (outLines T v ns answerTo r).1.Ok ∧ (outLines T v ns answerTo r).1.avoid = ns.avoid ∧
      (outLines T v ns answerTo r).2.isSome := by
  simp only [Result.shownIds] at hcov
  obtain ⟨hcov, hco⟩ := covers_append hcov
  obtain ⟨hca, hce⟩ := covers_append hcov
  have hev : v.event ∈ v.wireTys := List.mem_cons_of_mem _ List.mem_cons_self
  have rest : ∀ (ns1 : Names) (a : List Line), ns1.Ok → ns1.avoid = ns.avoid →
      (match writeAll (eventLine T v r.state.now) ns1 r.events with
        | (ns, none) => (ns, none)
        | (ns, some evs) => let o := writeAll (sentLine T r.state.now) ns r.out; (o.1, o.2.map (a ++ evs ++ ·))).1.Ok ∧
      (match writeAll (eventLine T v r.state.now) ns1 r.events with
        | (ns, none) => (ns, none)
        | (ns, some evs) => let o := writeAll (sentLine T r.state.now) ns r.out;
          (o.1, o.2.map (a ++ evs ++ ·))).1.avoid = ns.avoid ∧
      (match writeAll (eventLine T v r.state.now) ns1 r.events with
        | (ns, none) => (ns, none)
        | (ns, some evs) => let o := writeAll (sentLine T r.state.now) ns r.out;
          (o.1, o.2.map (a ++ evs ++ ·))).2.isSome := by
    intro ns1 a hok1 hav1
    have hevs := writeAll_ok (A := ns.avoid) (f := eventLine T v r.state.now) r.events (fun ev hev' ns' h' ha' => by
      obtain ⟨h1, h2, h3⟩ := Names.enc_ok h' (wire_encodes chk hev) ev (ha' ▸ covers_flatMap hce ev hev')
      exact ⟨h1, h2.trans ha', by simpa [eventLine] using h3⟩) ns1 hok1 hav1
    revert hevs
    generalize writeAll (eventLine T v r.state.now) ns1 r.events = q
    obtain ⟨nsq, evq⟩ := q
    intro hevs
    obtain ⟨evs, rfl⟩ := Option.isSome_iff_exists.1 hevs.2.2
    have houts := writeAll_ok (A := ns.avoid) (f := sentLine T r.state.now) r.out (fun o ho ns' h' ha' => by
      obtain ⟨hw1, hw2⟩ := Names.wire_ok h' o.id
      obtain ⟨h1, h2, h3⟩ := Names.enc_ok hw1 (wire_encodes chk (hout o ho)) o.input.2
        (hw2.trans ha' ▸ covers_flatMap hco o ho)
      exact ⟨h1, (h2.trans hw2).trans ha', by simpa [sentLine] using h3⟩) nsq hevs.1 hevs.2.1
    exact ⟨houts.1, houts.2.1, by simp [Option.isSome_map, houts.2.2]⟩
  unfold outLines
  cases answerTo with
  | none => exact rest ns [] h rfl
  | some to =>
    dsimp only
    have hl : (answerLine T ns r.state.now to r.outcome).1.Ok ∧
        (answerLine T ns r.state.now to r.outcome).1.avoid = ns.avoid ∧
        (answerLine T ns r.state.now to r.outcome).2.isSome := by
      revert hnf hans hrej hca
      cases r.outcome with
      | accepted | invalid => intros; exact ⟨h, rfl, rfl⟩
      | fault f => intro hnf; exact absurd rfl (hnf f)
      | answered w =>
        obtain ⟨t, x⟩ := w
        intro _ hans _ hca
        obtain ⟨h1, h2, h3⟩ := Names.enc_ok h (wire_encodes chk (hans _ rfl)) x hca
        simp only [answerLine]
        exact ⟨h1, h2, by simpa using h3⟩
      | rejected w =>
        obtain ⟨t, x⟩ := w
        intro _ _ hrej hca
        obtain ⟨h1, h2, h3⟩ := Names.enc_ok h (wire_encodes chk (hrej _ rfl)) x hca
        simp only [answerLine]
        exact ⟨h1, h2, by simpa using h3⟩
    revert hl
    generalize answerLine T ns r.state.now to r.outcome = q
    obtain ⟨ns1, l⟩ := q
    intro hl
    obtain ⟨l, rfl⟩ := Option.isSome_iff_exists.1 hl.2.2
    exact rest ns1 [l] hl.1 hl.2.1

end

section
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

theorem answerWire_ok {ns : Names} (h : ns.Ok) (o : Ty) (rj : Option Ty) (ho : o.encodes T = true)
    (hj : ∀ j, rj = some j → j.encodes T = true) (x : (answerTy o rj).den0)
    (hc : Covers ns.avoid (idsOf T (answerTy o rj) x)) :
    (ns.answerWire T o rj x).1.Ok ∧ (ns.answerWire T o rj x).1.avoid = ns.avoid ∧ (ns.answerWire T o rj x).2.isSome := by
  match rj, x with
  | some j, .inl (x, ()) =>
    have := Names.enc_ok h ho x fun s hs => hc s (by simp [answerTy, Ty.result, idsOf, idsOfAlts, idsOfs, hs])
    simpa [Names.answerWire] using this
  | some j, .inr (.inl (x, ())) =>
    have := Names.enc_ok h (hj j rfl) x fun s hs => hc s (by simp [answerTy, Ty.result, idsOf, idsOfAlts, idsOfs, hs])
    simpa [Names.answerWire] using this
  | none, x =>
    have := Names.enc_ok h ho x hc
    simpa [Names.answerWire] using this

/-- A run's step that faults nowhere writes its out lines. -/
theorem finish'_ok (chk : Smt.Checked P E T v) {run : Run v} (hinv : Inv P run.state) (hok : run.names.Ok)
    (input : Input v) (inLines : List Line) (answerTo : Option String) (k : Nat)
    (hnf : ∀ f, (step T v run.state input).outcome ≠ .fault f)
    (hcov : Covers run.names.avoid ((step T v run.state input).shownIds T)) :
    ∃ run', run.finish' T v input inLines answerTo k = .ok run' ∧ run'.state = (step T v run.state input).state ∧
      run'.names.Ok ∧ run'.names.avoid = run.names.avoid := by
  have hout : ∀ o ∈ (step T v run.state input).out, o.input.1 ∈ v.wireTys := fun o ho => by
    obtain ⟨p, hp, rfl⟩ := step_outsWait T run.state input o ho
    exact (atShapes_tys ((step_inv T chk.reach run.state hinv input).shaped p hp)).1
  have hw := outLines_ok chk hok answerTo _ hnf (step_outcome_tys T run.state input).1
    (step_outcome_tys T run.state input).2 hout hcov
  unfold Run.finish'
  revert hnf hw
  generalize step T v run.state input = r
  intro hnf hw
  cases ho : r.outcome with
  | fault f => exact absurd ho (hnf f)
  | _ =>
    all_goals
      simp only [pure, Except.pure]
      revert hw
      generalize outLines T v run.names answerTo r = q
      obtain ⟨ns, outs⟩ := q
      intro hw
      obtain ⟨outs, rfl⟩ := Option.isSome_iff_exists.1 hw.2.2
      exact ⟨_, rfl, rfl, hw.1, hw.2.1⟩

end

section
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

theorem caller_wire : v.caller ∈ v.wireTys := List.mem_cons_self

theorem command_wire (i : Fin v.commands.length) : (v.commands.get i).input ∈ v.wireTys := by
  simp only [ServiceV.wireTys]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_flatMap.2 ⟨_, List.get_mem _ _, List.mem_cons_self⟩)))))

theorem query_wire (i : Fin v.queries.length) : (v.queries.get i).input ∈ v.wireTys := by
  simp only [ServiceV.wireTys]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, List.get_mem _ _, List.mem_cons_self⟩)))))

theorem subscribe_wire (i : Fin v.subscribes.length) : (v.subscribes.get i).event ∈ v.wireTys := by
  simp only [ServiceV.wireTys]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨_, List.get_mem _ _, rfl⟩))))

/-- One input of a run that faults nowhere is written: its in line, its step and its out lines. -/
theorem runInput_ok (chk : Smt.Checked P E T v) {run : Run v} (hinv : Inv P run.state) (hok : run.names.Ok)
    (k : Nat) (x : Input v) (hnf : ∀ f, (step T v run.state x).outcome ≠ .fault f)
    (hcov : Covers run.names.avoid (x.ids T ++ (step T v run.state x).shownIds T)) :
    ∃ run', run.input T v k x = .ok run' ∧ run'.state = (step T v run.state x).state ∧ run'.names.Ok ∧
      run'.names.avoid = run.names.avoid := by
  obtain ⟨hcx, hcs⟩ := covers_append hcov
  -- A request: its caller and input are written, then the step.
  have request : ∀ (name : String) (caller : v.caller.den0) (value : WireVal), value.1 ∈ v.wireTys →
      Covers run.names.avoid (idsOf T v.caller caller ++ idsOf T value.1 value.2) →
      ∀ inp : Input v, (∀ f, (step T v run.state inp).outcome ≠ .fault f) →
      Covers run.names.avoid ((step T v run.state inp).shownIds T) →
      ∃ run', Run.input.request T v run k name inp caller value = .ok run' ∧
        run'.state = (step T v run.state inp).state ∧ run'.names.Ok ∧ run'.names.avoid = run.names.avoid := by
    intro name caller value hv hc inp hnf' hcs'
    obtain ⟨hc1, hc2⟩ := covers_append hc
    obtain ⟨h1, h2, h3⟩ := Names.enc_ok hok (wire_encodes chk caller_wire) caller hc1
    obtain ⟨h4, h5, h6⟩ := Names.enc_ok h1 (wire_encodes chk hv) value.2 (h2 ▸ hc2)
    unfold Run.input.request
    revert h1 h2 h3 h4 h5 h6
    generalize run.names.enc T v.caller caller = q1
    obtain ⟨ns1, c⟩ := q1
    intro h1 h2 h3
    obtain ⟨c, rfl⟩ := Option.isSome_iff_exists.1 h3
    dsimp only
    generalize ns1.enc T value.1 value.2 = q2
    obtain ⟨ns2, i⟩ := q2
    intro h4 h5 h6
    obtain ⟨i, rfl⟩ := Option.isSome_iff_exists.1 h6
    dsimp only
    simp only at h1 h2 h4 h5
    obtain ⟨run', hr, hs, ho, ha⟩ := finish'_ok chk (run := { run with names := ns2, requests := run.requests + 1 })
      hinv h4 inp _ (some (toString (run.requests + 1))) k hnf' (by simp only [h5, h2]; exact hcs')
    exact ⟨run', hr, hs, ho, ha.trans (h5.trans h2)⟩
  cases x with
  | command i caller input =>
    exact request _ caller ⟨_, input⟩ (command_wire i) hcx _ hnf hcs
  | query i caller input =>
    exact request _ caller ⟨_, input⟩ (query_wire i) hcx _ hnf hcs
  | answer to w =>
    obtain ⟨ty, value⟩ := w
    unfold Run.input
    dsimp only
    cases hp : run.state.pending.find? (·.id == to) with
    | none =>
      have : (step T v run.state (.answer to ⟨ty, value⟩)).outcome = .fault .answerUnmatched := by
        simp [step, hp]
      exact absurd this (hnf _)
    | some p =>
      dsimp only
      cases hty : Ty.same ty (answerTy p.request.output p.request.rejection) with
      | none =>
        have : (step T v run.state (.answer to ⟨ty, value⟩)).outcome = .fault .answerUnmatched := by
          simp [step, hp, hty]
        exact absurd this (hnf _)
      | some e =>
        obtain ⟨e⟩ := e
        subst e
        dsimp only
        have hpm := List.mem_of_find?_eq_some hp
        obtain ⟨-, hso, hsj⟩ := atShapes_tys (hinv.shaped p hpm)
        obtain ⟨hw1, hw2⟩ := Names.wire_ok hok p.id
        obtain ⟨h1, h2, h3⟩ := answerWire_ok hw1 p.request.output p.request.rejection (wire_encodes chk hso)
          (fun j hj => wire_encodes chk (hsj j hj)) value (hw2 ▸ hcx)
        revert hw1 hw2 h1 h2 h3
        generalize run.names.wire p.id = q1
        obtain ⟨ns1, wn⟩ := q1
        intro hw1 hw2
        generalize ns1.answerWire T p.request.output p.request.rejection value = q2
        obtain ⟨ns2, a⟩ := q2
        intro h1 h2 h3
        obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.1 h3
        simp only at h1 h2 hw2
        obtain ⟨run', hr, hs, ho, ha⟩ := finish'_ok chk (run := { run with names := ns2 }) hinv h1 _ _ none k hnf
          (by simp only [h2, hw2]; exact hcs)
        exact ⟨run', hr, hs, ho, ha.trans (h2.trans hw2)⟩
  | event i value =>
    unfold Run.input
    dsimp only
    obtain ⟨h1, h2, h3⟩ := Names.enc_ok hok (wire_encodes chk (subscribe_wire i)) value hcx
    revert h1 h2 h3
    generalize run.names.enc T (v.subscribes.get i).event value = q
    obtain ⟨ns1, w⟩ := q
    intro h1 h2 h3
    obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.1 h3
    dsimp only
    simp only at h1 h2
    obtain ⟨run', hr, hs, ho, ha⟩ := finish'_ok chk (run := { run with names := ns1 }) hinv h1 _ _ none k hnf
      (by simp only [h2]; exact hcs)
    exact ⟨run', hr, hs, ho, ha.trans h2⟩
  | clock t =>
    unfold Run.input
    exact finish'_ok chk hinv hok _ _ none k hnf hcs

end

section
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

theorem foldInputs_ok (chk : Smt.Checked P E T v) : (xs : List (Input v)) → (w : Run v) → (k : Nat) →
    Inv P w.state → w.names.Ok →
    Covers w.names.avoid (xs.flatMap (·.ids T) ++ (Tazuna.Ir.run T v w.state xs).2.flatMap (·.shownIds T)) →
    NoFaultRun T w.state xs →
    ∃ r, xs.foldlM (fun (run, k) x => do pure (← run.input T v (k + 1) x, k + 1)) (w, k) = .ok r
  | [], w, k, _, _, _, _ => ⟨(w, k), rfl⟩
  | x :: xs, w, k, hinv, hok, hcov, ⟨hnf, hrest⟩ => by
    have hc : Covers w.names.avoid (x.ids T ++ (step T v w.state x).shownIds T) := fun s hs => hcov s (by
      simp only [List.flatMap_cons, Tazuna.Ir.run, List.mem_append] at hs ⊢
      rcases hs with hs | hs
      · exact .inl (.inl hs)
      · exact .inr (.inl hs))
    obtain ⟨w', hw, hs, ho, ha⟩ := runInput_ok chk hinv hok (k + 1) x hnf hc
    have hcov' : Covers w'.names.avoid (xs.flatMap (·.ids T) ++
        (Tazuna.Ir.run T v w'.state xs).2.flatMap (·.shownIds T)) := fun s hs' => by
      rw [ha]
      refine hcov s ?_
      rw [hs] at hs'
      simp only [List.flatMap_cons, Tazuna.Ir.run, List.mem_append] at hs' ⊢
      rcases hs' with hs' | hs'
      · exact .inl (.inr hs')
      · exact .inr (.inr hs')
    have hinv' : Inv P w'.state := hs ▸ step_inv T chk.reach w.state hinv x
    obtain ⟨r, hr⟩ := foldInputs_ok chk xs w' (k + 1) hinv' ho hcov' (hs ▸ hrest)
    refine ⟨r, ?_⟩
    rw [List.foldlM_cons]
    dsimp only
    rw [hw]
    exact hr

theorem contains_outside {l : List IdV} {s : Str} (h : IdV.named s ∈ l) :
    (l.filterMap fun | .named s => some s.1 | .fresh .. => none).contains s.1 = true :=
  List.elem_iff.2 (List.mem_filterMap.2 ⟨_, h, rfl⟩)

/-- A run from the initial state that faults nowhere writes a trace: check's facts make every value it writes have a
wire form, and its names avoid every outside name it writes. -/
theorem traceOf_ok (chk : Smt.Checked P E T v) {xs : List (Input v)} (hnf : NoFaultRun T (State.init v) xs) :
    ∃ tr, traceOf T v xs = .ok tr := by
  obtain ⟨r, hr⟩ := foldInputs_ok chk xs { state := State.init v, names := { avoid := outsideNames T (State.init v) xs } }
    0 init_inv (Names.ok_avoid _) (fun s hs => contains_outside hs) hnf
  unfold traceOf
  rw [hr]
  exact ⟨_, rfl⟩

end

end Tazuna.Trace
