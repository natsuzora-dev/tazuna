import Tazuna.Smt.State
import Tazuna.Semantics.Emits

/-! The cone of influence of a step of an input kind, read off the code it runs: the constructors of the event it can
apply (`SymInput.evs`, behind `Step.step_events`), and the answer sites of the own effects its cascade can queue
(`SymInput.live`, behind `Step.begins_live`). Dead targets read the first; the cascade's encoding reads the second and
asks only for the own kinds the step can queue, and a pair of own kinds no kind can queue together gets no question
(`together`, `Layout.apart`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The declaration of the service's event type, where it is a custom type of the program's own. -/
def eventDecl (v : ServiceV) : Option Nat :=
  match v.event with
  | .adt i _ _ => if prelude.length ≤ i then some i else none
  | _ => none

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- Whether the kind is a clock line. -/
def SymInput.isClock : SymInput v shs n → Bool
  | .clock _ => true
  | _ => false

/-- The constructors of the event declaration `i` an answer of the type `t` can apply: its `on_answer`, a site of that
type, and the cascade's; none where a value the step starts from can hold an event. -/
def answerEvs (P : List AnySite) (v : ServiceV) (i : Nat) (t : Ty) : Option (List Nat) :=
  let ss := sitesOf P (.fn [t] (.list v.event))
  if v.quiet i && !t.mentions i && ss.all (fun s => !(Ty.tuple s.1).mentions i) then
    some (ss.flatMap (fun s => s.2.body.evs i (s.2.defs.evs i)) ++ v.cascadeEvs i)
  else none

/-- The constructors of the event declaration `i` a step of the kind can apply, read off the functions it runs
(`Step.step_events`); none where a value the step starts from can hold an event, or for a query. -/
def SymInput.evs (P : List AnySite) (i : Nat) : SymInput v shs n → Option (List Nat)
  | .command k _ _ => if v.quiet i then some ((v.commands.get k).decide.evs i ++ v.cascadeEvs i) else none
  | .answer k _ _ _ => answerEvs P v i (answerTy shs[k].output shs[k].rejection)
  | .unmatched t _ _ => answerEvs P v i t
  | .event k _ => if v.quiet i then some ((v.subscribes.get k).wrap.evs i ++ v.cascadeEvs i) else none
  | .clock _ => if v.quiet i then some (v.cascadeEvs i) else none
  | .query .. => none

/-- The answer sites of the own effects a step of the kind can queue: what `ServiceV.liveSites` writes for the events
the kind can apply and, but at a clock line, the machine states it can enter. None where the code cannot bound them,
and then the cascade asks for every own kind. -/
def SymInput.live (P : List AnySite) (inp : SymInput v shs n) : Option (List SiteId) :=
  match eventDecl v with
  | some i => (inp.evs P i).map fun ns => (v.liveSites i (fun k => ns.contains k) inp.isClock).map (·.2.2.site)
  | none => none

/-- What the cascade of a step of the kind keeps (`Step.LiveOk`), where the kind bounds its own effects. -/
def SymInput.LiveJ (P : List AnySite) (inp : SymInput v shs n) (a : Step.Acc v) : Prop :=
  ∀ i ns, eventDecl v = some i → inp.evs P i = some ns →
    Step.LiveOk i (· ∈ ns) (v.liveSites i (fun k => ns.contains k) inp.isClock) a

/-- Whether some kind of `inps` can have an effect answered at `s1` and one answered at `s2` waiting together: the own
effects it can queue (`SymInput.live`) take both sites, or it cannot bound them. -/
def together (P : List AnySite) (inps : List (SymInput v shs n)) (s1 s2 : SiteId) : Bool :=
  inps.any fun inp => match inp.live P with
    | some l => decide (s1 ∈ l ∧ s2 ∈ l)
    | none => true

theorem together_of {P : List AnySite} {inps : List (SymInput v shs n)} {inp : SymInput v shs n} (hm : inp ∈ inps)
    {s1 s2 : SiteId} (h : ∀ l, inp.live P = some l → s1 ∈ l ∧ s2 ∈ l) : together P inps s1 s2 = true := by
  refine List.any_eq_true.2 ⟨inp, hm, ?_⟩
  cases hl : inp.live P with
  | none => rfl
  | some l => exact decide_eq_true (h l hl)

end

/-- The site of the kept function an own effect runs at its answer. -/
def _root_.Tazuna.Ir.OwnEffectV.site {e : Ty} : OwnEffectV e → SiteId
  | .command _ _ _ _ _ f => f.site
  | .query _ _ _ _ _ f => f.site

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat} {M : Model} {L : Layout} (T : List TypeDecl)

theorem eventDecl_some {i : Nat} (h : eventDecl v = some i) : 15 ≤ i ∧ ∃ a vs, v.event = .adt i a vs := by
  unfold eventDecl at h
  split at h
  · rename_i j a vs he
    split at h
    · rename_i hle; cases h; exact ⟨hle, a, vs, he⟩
    · cases h
  · cases h

theorem decodeAnswer_some {t : Ty} {to value : Term} {x : Input v} (h : decodeAnswer M L t to value = some x) :
    ∃ m y, x = .answer m ⟨t, y⟩ := by
  unfold decodeAnswer at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨m, -, y, -, rfl⟩ := h
    exact ⟨m, _, rfl⟩
  · cases h

theorem answerEvs_some {P : List AnySite} {i : Nat} {t : Ty} {ns : List Nat} (h : answerEvs P v i t = some ns) :
    v.quiet i = true ∧ (∀ k ∈ v.cascadeEvs i, k ∈ ns) ∧ t.mentions i = false ∧
      ∀ s ∈ sitesOf P (.fn [t] (.list v.event)),
        (Ty.tuple s.1).mentions i = false ∧ ∀ k ∈ s.2.body.evs i (s.2.defs.evs i), k ∈ ns := by
  unfold answerEvs at h
  dsimp only at h
  split at h
  · rename_i hq
    cases h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hq
    obtain ⟨⟨hq, ht⟩, hs⟩ := hq
    refine ⟨hq, fun k hk => List.mem_append_right _ hk, ht, fun s hs' => ⟨by simpa using hs s hs', fun k hk => ?_⟩⟩
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨s, hs', hk⟩)
  · cases h

/-- What `SymInput.evs` reads is what `Step.step_events` needs of every input the kind decodes to. -/
theorem evs_entry {P : List AnySite} {i : Nat} {inp : SymInput v shs n} {ns : List Nat} (h : inp.evs P i = some ns)
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x) :
    Quiet i v ∧ (∀ k ∈ v.cascadeEvs i, k ∈ ns) ∧ Step.EntryOk P i (· ∈ ns) x ∧ x.isClock = inp.isClock := by
  cases inp with
  | command k caller input =>
    simp only [SymInput.evs] at h
    split at h
    · rename_i hq
      cases h
      simp only [SymInput.decode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
      obtain ⟨c, -, y, -, rfl⟩ := hx
      exact ⟨quiet_facts hq, fun k hk => List.mem_append_right _ hk,
        .inr fun k hk => List.mem_append_left _ hk, rfl⟩
    · cases h
  | answer k j to value =>
    obtain ⟨hq, hcas, ht, hs⟩ := answerEvs_some h
    obtain ⟨m, y, rfl⟩ := decodeAnswer_some hx
    exact ⟨quiet_facts hq, hcas, ⟨ht, hs⟩, rfl⟩
  | unmatched t to value =>
    obtain ⟨hq, hcas, ht, hs⟩ := answerEvs_some h
    obtain ⟨m, y, rfl⟩ := decodeAnswer_some hx
    exact ⟨quiet_facts hq, hcas, ⟨ht, hs⟩, rfl⟩
  | event k value =>
    simp only [SymInput.evs] at h
    split at h
    · rename_i hq
      cases h
      simp only [SymInput.decode, Option.map_eq_some_iff] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨quiet_facts hq, fun k hk => List.mem_append_right _ hk, fun k hk => List.mem_append_left _ hk, rfl⟩
    · cases h
  | clock time =>
    simp only [SymInput.evs] at h
    split at h
    · rename_i hq
      cases h
      simp only [SymInput.decode, Option.map_eq_some_iff] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨quiet_facts hq, fun k hk => hk, trivial, rfl⟩
    · cases h
  | query => cases h

theorem evs_quiet {P : List AnySite} {i : Nat} {inp : SymInput v shs n} {ns : List Nat} (h : inp.evs P i = some ns) :
    Quiet i v ∧ ∀ k ∈ v.cascadeEvs i, k ∈ ns := by
  cases inp with
  | answer k j to value =>
    obtain ⟨hq, hcas, -, -⟩ := answerEvs_some h
    exact ⟨quiet_facts hq, hcas⟩
  | unmatched t to value =>
    obtain ⟨hq, hcas, -, -⟩ := answerEvs_some h
    exact ⟨quiet_facts hq, hcas⟩
  | query => cases h
  | _ =>
    simp only [SymInput.evs] at h
    split at h
    · rename_i hq
      cases h
      exact ⟨quiet_facts hq, fun k hk => by simp [hk]⟩
    · cases h

variable {P : List AnySite} {E : List AnyEffectSite}

/-- An own effect the cascade of a sliced kind queues has its answer site among the kind's. -/
theorem liveJ_site {inp : SymInput v shs n} {a : Step.Acc v} (ha : inp.LiveJ P a) :
    ∀ o ∈ a.own, ∀ l, inp.live P = some l → o.site ∈ l := by
  intro o ho l hl
  unfold SymInput.live at hl
  split at hl
  · rename_i i hi
    obtain ⟨ns, hns, rfl⟩ := Option.map_eq_some_iff.1 hl
    have hr := (ha i ns hi hns).2 o ho
    cases o with
    | command _ _ _ _ _ f => exact List.mem_map.2 ⟨_, hr, rfl⟩
    | query _ _ _ _ _ f => exact List.mem_map.2 ⟨_, hr, rfl⟩
  · cases hl

/-- An internal step keeps what the cascade of a sliced kind keeps. -/
theorem liveJ_run (hv : v.Reach P E) {inp : SymInput v shs n} {a : Step.Acc v} (ha : inp.LiveJ P a)
    (o : OwnEffectV v.event) (ho : o ∈ a.own) {a' : Step.Acc v} (h : Step.runOwn T a o = .ok a') : inp.LiveJ P a' := by
  intro i ns hi hns
  obtain ⟨hq, hc⟩ := evs_quiet hns
  exact Step.liveOk_runOwn T (eventDecl_some hi).1 hq hc hv (fun k => ⟨List.elem_eq_true_of_mem, List.mem_of_elem_eq_true⟩)
    (fun _ h => h) a (ha i ns hi hns) o ((ha i ns hi hns).1.own o ho) h

/-- So does a step of the cascade, which runs a waiting effect from the queue without it. -/
theorem liveJ_pick (hv : v.Reach P E) {inp : SymInput v shs n} {a : Step.Acc v} (ha : inp.LiveJ P a) {j : Nat}
    (hj : j < a.own.length) {a' : Step.Acc v} (h : Step.runOwn T { a with own := a.own.eraseIdx j } a.own[j] = .ok a') :
    inp.LiveJ P a' := by
  intro i ns hi hns
  obtain ⟨hq, hc⟩ := evs_quiet hns
  exact Step.liveOk_runOwn T (eventDecl_some hi).1 hq hc hv (fun k => ⟨List.elem_eq_true_of_mem, List.mem_of_elem_eq_true⟩)
    (fun _ h => h) _ ((ha i ns hi hns).sub fun _ => List.mem_of_mem_eraseIdx) _
    ((ha i ns hi hns).1.own _ (List.getElem_mem hj)) h

theorem liveJ_apply (hv : v.Reach P E) {inp : SymInput v shs n} (s : State v) (evs : List v.event.den0)
    (hok : ∀ i ns, eventDecl v = some i → inp.evs P i = some ns →
      ∀ ev ∈ evs, ∀ h : v.event.isData = true, Ok i (· ∈ ns) v.event (Ty.up _ h ev))
    {a : Step.Acc v} (h : Step.applyEvents T { state := s } evs = .ok a) : inp.LiveJ P a := by
  intro i ns hi hns
  obtain ⟨hq, hc⟩ := evs_quiet hns
  have hi15 := (eventDecl_some hi).1
  exact ⟨Step.applyEvents_ok T hi15 hq hc evs (hok i ns hi hns) _ (Step.accOk_start false s) h,
    Step.applyEvents_live T hi15 hq hc hv (fun k => ⟨List.elem_eq_true_of_mem, List.mem_of_elem_eq_true⟩) (fun _ h => h) evs
      (hok i ns hi hns) _ (fun _ h => by cases h) h⟩

theorem liveJ_clock (hv : v.Reach P E) {time : Term} (s : State v) (fuel : Nat) {s' : State v}
    {effs : List (Sender × EffectV v.event)} (hf : Step.fire s fuel = some (s', effs)) {a : Step.Acc v}
    (h : Step.start { state := s' } effs = .ok a) : (SymInput.clock (shs := shs) (slots := n) time).LiveJ P a := by
  intro i ns hi hns
  obtain ⟨hq, hc⟩ := evs_quiet hns
  have hi15 := (eventDecl_some hi).1
  exact ⟨Step.start_ok _ effs (Step.accOk_start false s') (Step.fire_ok hi15 hq hc _ _ hf) (fun h => by cases h) h,
    Step.start_queue _ _ h (fun _ h => by cases h)
      (Step.fire_live hi15 hq hc hv (fun k => ⟨List.elem_eq_true_of_mem, List.mem_of_elem_eq_true⟩) (fun _ h => h) rfl _ _ hf)⟩

theorem liveJ_command (hv : v.Reach P E) (k : Fin v.commands.length) {sc si : Term} (s : State v)
    (caller : (Ty.origin v.caller).den0) (input : (v.commands.get k).input.den0) {evs : List v.event.den0}
    (hdec : (v.commands.get k).decide.fn (Step.ctx s s.records caller input, ()) = .inl (evs, ()))
    {a : Step.Acc v} (h : Step.applyEvents T { state := { s with fresh := s.fresh + 1 } } evs = .ok a) :
    (SymInput.command (shs := shs) (slots := n) k sc si).LiveJ P a := by
  refine liveJ_apply T hv _ evs (fun i ns hi hns => ?_) h
  simp only [SymInput.evs] at hns
  split at hns
  · rename_i hqb
    cases hns
    have hq := quiet_facts hqb
    have hmem : v.commands.get k ∈ v.commands := List.get_mem _ _
    obtain ⟨hin, -, hΓ⟩ := hq.commands _ hmem
    have h15 := (eventDecl_some hi).1
    simp only [List.get_eq_getElem] at hin
    have hf := Fun.ok_eval (okV := (· ∈ (v.commands.get k).decide.evs i ++ v.cascadeEvs i)) (eventDecl_some hi).1
      (v.commands.get k).decide (fun k hk => List.mem_append_left _ hk) (oks_free _ hΓ _)
    have hps : (Ty.tuple [Ty.ctx v.records (v.commands.get k).input v.caller]).isData = true := by
      have := (v.commands.get k).decide.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
    exact Step.result_events _ hps _ (hf _ (oks_free _ (by
      simp [Ty.ctx, Ty.origin, Ty.mentionsL, Ty.mentions, Ty.mentionsLL, hin, hq.records, hq.caller]; omega) _)) hdec
  · cases hns

theorem liveJ_event (hv : v.Reach P E) (k : Fin v.subscribes.length) {sv : Term} (s : State v)
    (value : (v.subscribes.get k).event.den0) {a : Step.Acc v}
    (h : Step.applyEvents T { state := s } [(v.subscribes.get k).wrap.fn (value, ())] = .ok a) :
    (SymInput.event (shs := shs) (slots := n) k sv).LiveJ P a := by
  refine liveJ_apply T hv _ _ (fun i ns hi hns => ?_) h
  simp only [SymInput.evs] at hns
  split at hns
  · rename_i hqb
    cases hns
    have hq := quiet_facts hqb
    intro ev hev he
    simp only [List.mem_singleton] at hev
    subst hev
    have hsub : v.subscribes.get k ∈ v.subscribes := List.get_mem _ _
    obtain ⟨hevt, hΓ⟩ := hq.subscribes _ hsub
    have hps : (Ty.tuple [(v.subscribes.get k).event]).isData = true := by
      have := (v.subscribes.get k).wrap.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
    erw [Fun.fn_app _ hps he, Ty.up_down]
    exact Fun.ok_eval (eventDecl_some hi).1 _ (fun k hk => List.mem_append_left _ hk) (oks_free _ hΓ _) _
      (oks_free _ (by simp only [Ty.mentionsL, hevt]; rfl) _)
  · cases hns

/-- So does the cascade of an answer of the type `t` that a kept function of the program applies, where the kind reads
the constructors such an answer can apply. -/
theorem liveJ_onAnswer (hv : v.Reach P E) {inp : SymInput v shs n} {t : Ty}
    (hevs : ∀ i ns, inp.evs P i = some ns → answerEvs P v i t = some ns)
    (f : Fun (.fn [t] (.list v.event))) (hf : f.asSite ∈ P) (s : State v) (value : t.den0) {a : Step.Acc v}
    (h : Step.applyEvents T { state := s } (f.fn (value, ())) = .ok a) : inp.LiveJ P a := by
  refine liveJ_apply T hv _ _ (fun i ns hi hns => ?_) h
  obtain ⟨-, -, ht, hs⟩ := answerEvs_some (hevs i ns hns)
  have hmem : (⟨f.Γ, ⟨f.site, f.G, f.defs, f.hΓ, f.ht, f.body⟩⟩ : (Γ : List Ty) × Site Γ _) ∈
      sitesOf P (.fn [t] (.list v.event)) := by
    simp only [sitesOf, List.mem_filterMap]
    exact ⟨_, hf, by simp [Fun.asSite, Ty_same_rfl]⟩
  obtain ⟨hΓ, hev⟩ := hs _ hmem
  have hps : (Ty.tuple [t]).isData = true := by
    have := f.ht; simp only [Ty.isData, Bool.and_eq_true] at this; exact this.1
  have hf' := Fun.ok_eval (okV := (· ∈ ns)) (eventDecl_some hi).1 f hev (oks_free _ hΓ _)
  exact fn_events _ hps (value, ()) (hf' _ (oks_free _ (by simp [Ty.mentionsL, ht]) _))

theorem liveJ_answer (hv : v.Reach P E) {k : Fin shs.length} {j : Fin n} {toT valT : Term}
    (hin : (⟨shs[k].answerΓ, _, shs[k].onAnswer⟩ : AnySite) ∈ P) (s : State v)
    (value : (answerTy shs[k].output shs[k].rejection).den0)
    (env : (Ty.tuple shs[k].answerΓ).den0) {a : Step.Acc v}
    (h : Step.applyEvents T { state := s } ((shs[k].onAnswer.fn env).fn (value, ())) = .ok a) :
    (SymInput.answer k j toT valT).LiveJ P a :=
  liveJ_onAnswer T hv (fun _ _ h => by simpa [SymInput.evs] using h) (shs[k].onAnswer.fn env) hin s value h

end

end Tazuna.Smt
