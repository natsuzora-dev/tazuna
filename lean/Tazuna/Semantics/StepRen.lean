import Tazuna.Semantics.StepRename
import Tazuna.Semantics.ShiftOrder

/-! The step does not read the order a bag or table is stored in, the names its counters and wire ids happen to have,
nor where time starts. Two states are related by a renaming `R` when their records relate under `R` (bags and tables
as multisets, each fresh id's counter renamed, instants moved by `R`'s shift), the second's time is the first's moved,
every counter from the first's `fresh` on and every wire id from its `nextId` on is renamed to the second's moved as
far, and every other part relates item by item, in the same order: instances, pending requests, waiting own effects,
events and out lines (`StateRen`). Where `R` keeps the order of the counters it relates (`PBij.Mono`), as numbering
them by rank does, stepping such states on such inputs gives such results (`step_ren`). No spec can write an instant
or a counter, and the canonical order compares fresh ids only by their counters' order, so a step can only move,
compare and copy what it is given (Lamport, "Real-Time Model Checking is Really Simple", 2005). `StepRename` relates
the collections only as multisets, since a renaming that reorders counters reorders keys; one that keeps their order
keeps the canonical order of instance keys (`machineStep`, `Ty.cmp_shift`), so every effect starts, every own command
runs and every wire id is given in the same order. -/

namespace Tazuna.Ir

theorem PBij.rel_beq {W : PBij} {a b c d : Nat} (h : W.rel a b) (h' : W.rel c d) : (a == c) = (b == d) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun e => by subst e; exact W.func h h', fun e => by subst e; exact W.inj h h'⟩

theorem from_succ {W : PBij} {a b : Nat} (h : ∀ k, W.rel (a + k) (b + k)) : ∀ k, W.rel (a + 1 + k) (b + 1 + k) :=
  fun k => by rw [Nat.add_assoc, Nat.add_assoc]; exact h (1 + k)

theorem from_zero {W : PBij} {a b : Nat} (h : ∀ k, W.rel (a + k) (b + k)) : W.rel a b := h 0

/-- Instants related by a shift compare alike. -/
theorem PBij.point_ms_iff {R : PBij} {a a' b b' : Int} (ha : R.point .ms a a') (hb : R.point .ms b b') :
    (a = b ↔ a' = b') ∧ (a ≤ b ↔ a' ≤ b') ∧ (a < b ↔ a' < b') := by
  rw [PBij.point_ms_eq ha, PBij.point_ms_eq hb]; omega

theorem forall2_of_map_eq {α γ : Type} {f : α → γ} : {xs ys : List α} → xs.map f = ys.map f →
    Forall2 (fun a b => f a = f b) xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨h.1, forall2_of_map_eq h.2⟩
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem forall2_flatMap2 {α β γ δ : Type} {r : α → β → Prop} {r' : γ → δ → Prop} {f : α → List γ} {g : β → List δ}
    (hfg : ∀ a b, r a b → Forall2 r' (f a) (g b)) : {xs : List α} → {ys : List β} → Forall2 r xs ys →
    Forall2 r' (xs.flatMap f) (ys.flatMap g)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => by
    simp only [List.flatMap_cons]; exact forall2_append (hfg _ _ h) (forall2_flatMap2 hfg hs)

/-- Values related by a renaming that keeps the counters' order, put in the canonical order, relate item by item:
items of one Erlang term may change places, and such a renaming keeps the order (`Ty.cmp_shift`). -/
theorem Ty.sortBy_ren (T : List TypeDecl) {R : PBij} (hmo : R.Mono) {t : Ty} (hc : t.comparable = true)
    (ho : t.ordered T = true) {xs ys : List t.den0} (h : Multi (Ty.rel0 R t) xs ys) :
    Forall2 (Ty.rel0 R t) (Ty.sortBy T t xs) (Ty.sortBy T t ys) := by
  obtain ⟨zs, hz, hp⟩ := h
  have h1 : Forall2 (Ty.rel0 R t) (Ty.sortBy T t xs) (Ty.sortBy T t zs) :=
    forall2_mergeSort hz fun a b a' b' ha hb => by
      show (Erl.cmp _ _).isLE = (Erl.cmp _ _).isLE
      rw [Ty.cmp_shift T hmo t ho ha hb]
  have hsort : ∀ l : List t.den0, (Ty.sortBy T t l).map (Ty.erl T t) = Erl.sort (l.map (Ty.erl T t)) := fun l => by
    unfold Ty.sortBy Erl.sort
    exact List.map_mergeSort (fun _ _ _ _ => rfl)
  have h2 : (Ty.sortBy T t zs).map (Ty.erl T t) = (Ty.sortBy T t ys).map (Ty.erl T t) := by
    rw [hsort, hsort]; exact (Erl.sort_eq_iff _ _).2 (hp.map _)
  exact forall2_imp (fun _ _ ⟨_, h, e⟩ => Ty.rel0_deq_right hc h ((Ty.erl_iff T t ho _ _).2 e))
    (forall2_comp h1 (forall2_of_map_eq h2))

namespace Step

section Machine
variable {r e : Ty} {R : PBij}

/-- Instances related by `R`, item by item. -/
abbrev Insts.Ren (R : PBij) {m : MachineV r e} : List (Instance m) → List (Instance m) → Prop :=
  Forall2 (Instance.Rel R)

def Machines.Ren (R : PBij) : {ms : List (MachineV r e)} → Machines ms → Machines ms → Prop
  | _, .nil, .nil => True
  | _, .cons l rest, .cons l' rest' => Insts.Ren R l l' ∧ Machines.Ren R rest rest'

theorem reactKey_ren {m : MachineV r e} (hm : m.Equi) {insts insts' : List (Instance m)}
    (hl : Insts.Ren R insts insts') {records records' : r.den0} (hrec : Ty.rel0 R r records records')
    {now now' : Int} (hnow : R.point .ms now now') {ev ev' : e.den0}
    (hev : Ty.rel0 R e ev ev') {k k' : m.key.den0} (hk : Ty.rel0 R m.key k k') :
    Reacted.Rel R (reactKey m insts records now ev k) (reactKey m insts' records' now' ev' k') := by
  unfold reactKey
  have hf := forall2_find? (p := (m.key.deq0 k ·.key)) (q := (m.key.deq0 k' ·.key))
    (fun a b hab => Ty.rel0_deq m.key hm.key hk hab.1) hl
  revert hf
  generalize insts.find? _ = a
  generalize insts'.find? _ = b
  intro hf
  cases hf with
  | none => exact enter_rel hm hrec hnow hk (hm.self _).initial
  | @some i i' hi =>
    dsimp only
    have hon := (hm.self R).on (.inl (i.key, i.state, records, now, ()), ev, ())
      (.inl (i'.key, i'.state, records', now', ()), ev', ()) ⟨⟨hi.1, hi.2, hrec, hnow, trivial⟩, hev, trivial⟩
    revert hon
    generalize m.on.fn (.inl (i.key, i.state, records, now, ()), ev, ()) = x
    generalize m.on.fn (.inl (i'.key, i'.state, records', now', ()), ev', ()) = y
    intro hon
    match x, y, hon with
    | .inr (.inl (s, ())), .inr (.inl (s', ())), ⟨hs, _⟩ => exact enter_rel hm hrec hnow hi.1 hs
    | .inl (), .inl (), _ => exact ⟨hi, trivial⟩

theorem machineStep_ren (T : List TypeDecl) (hmo : R.Mono) {m : MachineV r e} (hm : m.Equi) (ho : m.key.ordered T = true)
    {records records' : r.den0} (hrec : Ty.rel0 R r records records') {now now' : Int}
    (hnow : R.point .ms now now') {ev ev' : e.den0} (hev : Ty.rel0 R e ev ev')
    {insts insts' : List (Instance m)} (hl : Insts.Ren R insts insts') :
    Insts.Ren R (machineStep T records now ev m insts).1 (machineStep T records' now' ev' m insts').1 ∧
      Forall2 (Started.Rel R) (machineStep T records now ev m insts).2
        (machineStep T records' now' ev' m insts').2 := by
  have hb : Multi (Ty.rel0 R m.key) (m.instances.fn (records, ())) (m.instances.fn (records', ())) :=
    (hm.self R).instances _ _ ⟨hrec, trivial⟩
  have hd : Multi (Ty.rel0 R m.key) (dedupBy m.key.deq0 (m.instances.fn (records, ())))
      (dedupBy m.key.deq0 (m.instances.fn (records', ()))) := by
    obtain ⟨zs, h, hz⟩ := hb
    exact ((Multi.of_forall2 (forall2_dedupBy (f := m.key.deq0) (f' := m.key.deq0)
      (fun _ _ _ _ => Ty.rel0_deq m.key hm.key) h)).comp
      (dedupBy_perm_multi (Ty.canon_iff m.key hm.key) hz)).imp fun _ _ ⟨_, h1, h2⟩ => Ty.rel0_deq_right hm.key h1 h2
  have hr := forall2_map2 (r' := Reacted.Rel R) (fun _ _ hk => reactKey_ren hm hl hrec hnow hev hk)
    (Ty.sortBy_ren T hmo hm.key ho hd)
  exact ⟨forall2_map2 (fun _ _ h => h.1) hr, forall2_flatMap2 (fun _ _ h => h.2) hr⟩

theorem reactMachines_ren (T : List TypeDecl) (hmo : R.Mono) {records records' : r.den0}
    (hrec : Ty.rel0 R r records records') {now now' : Int} (hnow : R.point .ms now now')
    {ev ev' : e.den0} (hev : Ty.rel0 R e ev ev') : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.Equi ∧ m.key.ordered T = true) → {l l' : Machines ms} → Machines.Ren R l l' →
    Machines.Ren R (reactMachines T records now ev l).1 (reactMachines T records' now' ev' l').1 ∧
      Forall2 (Started.Rel R) (reactMachines T records now ev l).2
        (reactMachines T records' now' ev' l').2
  | [], _, .nil, .nil, _ => ⟨trivial, trivial⟩
  | _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hx, hrest⟩ := h
    have hm := hms _ List.mem_cons_self
    have h1 := machineStep_ren T hmo hm.1 hm.2 hrec hnow hev hx
    have h2 := reactMachines_ren T hmo hrec hnow hev (fun m h => hms m (List.mem_cons_of_mem _ h)) hrest
    simp only [reactMachines]
    exact ⟨⟨h1.1, h2.1⟩, forall2_append h1.2 h2.2⟩

end Machine

variable {v : ServiceV} {R : Ren}

/-- States related by `R`, item by item, with the counters and wire ids they give next renamed alike. -/
def StateRen (R : Ren) (s s' : State v) : Prop :=
  Ty.rel0 R.ctr v.records s.records s'.records ∧ Machines.Ren R.ctr s.machines s'.machines ∧
    Forall2 (Pending.Rel R) s.pending s'.pending ∧ R.ctr.point .ms s.now s'.now ∧
    (∀ k, R.ctr.rel (s.fresh + k) (s'.fresh + k)) ∧ ∀ k, R.wire.rel (s.nextId + k) (s'.nextId + k)

/-- Steps in progress related by `R`, item by item. -/
def AccRen (R : Ren) (a a' : Acc v) : Prop :=
  StateRen R a.state a'.state ∧ Forall2 (Ty.rel0 R.ctr v.event) a.events a'.events ∧
    Forall2 (OutLine.Rel R) a.out a'.out ∧ Forall2 (OwnEffectV.Rel R.ctr) a.own a'.own

/-- What runs from such steps end in: the same fault on both sides, or such steps. -/
def ExRen (R : Ren) : Except Fault (Acc v) → Except Fault (Acc v) → Prop
  | .error f, .error f' => f = f'
  | .ok a, .ok a' => AccRen R a a'
  | _, _ => False

theorem AccRen.ofState {s s' : State v} (h : StateRen R s s') :
    AccRen R ({ state := s } : Acc v) { state := s' } :=
  ⟨h, trivial, trivial, trivial⟩

theorem ExRen.bind {x x' : Except Fault (Acc v)} (h : ExRen R x x') {f g : Acc v → Except Fault (Acc v)}
    (hfg : ∀ b b', AccRen R b b' → ExRen R (f b) (g b')) : ExRen R (x >>= f) (x' >>= g) := by
  match x, x', h with
  | .error _, .error _, _ => trivial
  | .ok b, .ok b', h => exact hfg b b' h

/-- The machines and reactions with their functions respecting every renaming, and keys in a canonical order. -/
structure Ordered (T : List TypeDecl) (v : ServiceV) : Prop where
  equi : v.Equivariant
  keys : ∀ m ∈ v.machines, m.key.ordered T = true

variable {T : List TypeDecl}

theorem react_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {s s' : State v} (hs : StateRen R s s') {ev ev' : v.event.den0}
    (hev : Ty.rel0 R.ctr v.event ev ev') :
    StateRen R (react T s ev).1 (react T s' ev').1 ∧
      Forall2 (Started.Rel R.ctr) (react T s ev).2 (react T s' ev').2 := by
  obtain ⟨hrec, hmach, hpend, hnow, hf, hn⟩ := hs
  have hrec' : Ty.rel0 R.ctr v.records (v.apply.fn (.inl (s.records, s.now, ()), ev, ()))
      (v.apply.fn (.inl (s'.records, s'.now, ()), ev', ())) :=
    (ho.equi.self R.ctr).apply _ _ ⟨⟨hrec, hnow, trivial⟩, hev, trivial⟩
  have hm := reactMachines_ren T hmo hrec' hnow hev (fun m hm => ⟨ho.equi.machines m hm, ho.keys m hm⟩) hmach
  unfold react
  dsimp only
  refine ⟨⟨hrec', hm.1, hpend, hnow, hf, hn⟩, forall2_append hm.2 ?_⟩
  have hx : ∀ x ∈ v.reactions, Forall2 (Started.Rel R.ctr)
      ((x.effectsAt ev (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) s.now).map (.reaction x.name, ·))
      ((x.effectsAt ev' (v.apply.fn (.inl (s'.records, s'.now, ()), ev', ())) s'.now).map (.reaction x.name, ·)) :=
    fun x hx => forall2_map2 (fun _ _ h => ⟨.reaction x.name, h⟩)
      (EffectFun.apply_rel x.react ((ho.equi.self R.ctr).reactions x hx) ⟨⟨hrec', hnow, trivial⟩, hev, trivial⟩)
  clear hm hpend
  revert hx
  induction v.reactions with
  | nil => intro; trivial
  | cons x xs ih =>
    intro hx
    simp only [List.flatMap_cons]
    exact forall2_append (hx x List.mem_cons_self) (ih fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem start_ren : {effs effs' : List (Sender × EffectV v.event)} →
    Forall2 (Started.Rel R.ctr) effs effs' → {a a' : Acc v} → AccRen R a a' →
    ExRen R (start a effs) (start a' effs')
  | [], [], _, _, _, ha => ha
  | (snd, eff) :: effs, (snd', eff') :: effs', ⟨⟨hs, he⟩, h⟩, a, a', ha => by
    unfold start
    rw [List.foldlM_cons, List.foldlM_cons]
    cases he with
    | @request r r' hrr =>
      dsimp only
      rw [← RequestV.ownerIn_rel hrr v.declared]
      cases r.ownerIn v.declared with
      | none => cases hrr; rfl
      | some x =>
        obtain ⟨⟨hrec, hmach, hpend, hnow, hf, hn⟩, hev, hout, hown⟩ := ha
        have hline : OutLine.Rel R ⟨a.state.nextId, x, r.name, ⟨r.input, r.value⟩⟩
            ⟨a'.state.nextId, x, r'.name, ⟨r'.input, r'.value⟩⟩ := by
          cases hrr with
          | mk _ _ _ _ hv _ _ => exact ⟨from_zero hn, rfl, rfl, .mk hv⟩
        exact start_ren h ⟨⟨hrec, hmach, forall2_append hpend ⟨⟨from_zero hn, hs, rfl, hrr⟩, trivial⟩, hnow, hf,
          from_succ hn⟩, hev, forall2_append hout ⟨hline, trivial⟩, hown⟩
    | command name c i j hval hf =>
      obtain ⟨hst, hev, hout, hown⟩ := ha
      exact start_ren h ⟨hst, hev, hout, forall2_append hown ⟨.command _ _ _ _ hval hf, trivial⟩⟩
    | query name c i o hval hf =>
      obtain ⟨hst, hev, hout, hown⟩ := ha
      exact start_ren h ⟨hst, hev, hout, forall2_append hown ⟨.query _ _ _ _ hval hf, trivial⟩⟩
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

theorem applyEvents_ren (ho : Ordered T v) (hmo : R.ctr.Mono) : {evs evs' : List v.event.den0} →
    Forall2 (Ty.rel0 R.ctr v.event) evs evs' → {a a' : Acc v} → AccRen R a a' →
    ExRen R (applyEvents T a evs) (applyEvents T a' evs')
  | [], [], _, _, _, ha => ha
  | ev :: evs, ev' :: evs', ⟨hev, h⟩, a, a', ha => by
    unfold applyEvents
    rw [List.foldlM_cons, List.foldlM_cons]
    have hr := react_ren ho hmo ha.1 hev
    obtain ⟨_, hevs, hout, hown⟩ := ha
    refine (start_ren hr.2 (a := { a with state := (react T a.state ev).1, events := a.events ++ [ev] })
      (a' := { a' with state := (react T a'.state ev').1, events := a'.events ++ [ev'] })
      ⟨hr.1, forall2_append hevs ⟨hev, trivial⟩, hout, hown⟩).bind fun b b' hb => ?_
    exact applyEvents_ren ho hmo h hb
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

/-- What a command's runs from such steps end in. -/
def RanRen (R : Ren) {j : Ty} : Except Fault (Ran v j) → Except Fault (Ran v j) → Prop
  | .error f, .error f' => f = f'
  | .ok (.invalid rs), .ok (.invalid rs') => rs = rs'
  | .ok (.rejected a x), .ok (.rejected a' x') => AccRen R a a' ∧ Ty.rel0 R.ctr j x x'
  | .ok (.accepted a), .ok (.accepted a') => AccRen R a a'
  | _, _ => False

theorem execCommand_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {a a' : Acc v} (ha : AccRen R a a')
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c c' : (Ty.origin v.caller).den0}
    (hc : Ty.rel0 R.ctr (Ty.origin v.caller) c c') {i i' : x.input.den0}
    (hi : Ty.rel0 R.ctr x.input i i') :
    RanRen R (execCommand T a x c i) (execCommand T a' x c' i') := by
  obtain ⟨hcl, hacc, hdec, hens⟩ := (ho.equi.self R.ctr).commands x hx
  unfold execCommand
  rw [admit_rel ho.equi hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => rfl
  | nil =>
    dsimp only
    have hcx : Ty.rel0 R.ctr (Ty.ctx v.records x.input v.caller) (ctx a.state a.state.records c i)
        (ctx a'.state a'.state.records c' i') := ⟨ha.1.1, hi, hc, ha.1.2.2.2.1, from_zero ha.1.2.2.2.2.1, trivial⟩
    have hd := hdec (ctx a.state a.state.records c i, ()) (ctx a'.state a'.state.records c' i', ()) ⟨hcx, trivial⟩
    revert hd
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = dc
    generalize x.decide.fn (ctx a'.state a'.state.records c' i', ()) = dc'
    intro hd
    obtain ⟨⟨hrec, hmach, hpend, hnow, hf, hn⟩, hevs0, hout, hown⟩ := ha
    have ha1 : AccRen R { a with state := { a.state with fresh := a.state.fresh + 1 } }
        { a' with state := { a'.state with fresh := a'.state.fresh + 1 } } :=
      ⟨⟨hrec, hmach, hpend, hnow, from_succ hf, hn⟩, hevs0, hout, hown⟩
    match dc, dc', hd with
    | .inl (evs, ()), .inl (evs', ()), ⟨hevs, _⟩ =>
      dsimp only
      have he := applyEvents_ren ho hmo hevs ha1
      revert he
      generalize applyEvents T _ evs = y
      generalize applyEvents T _ evs' = y'
      intro he
      match y, y', he with
      | .error _, .error _, h => exact h
      | .ok b, .ok b', hb =>
        show RanRen R (match broken _ with | _ :: _ => _ | [] => _) (match broken _ with | _ :: _ => _ | [] => _)
        rw [broken_rel (hens (ctx a.state a.state.records c i, b.state.records, ())
          (ctx a'.state a'.state.records c' i', b'.state.records, ()) ⟨hcx, hb.1.1, trivial⟩)]
        cases broken (x.ensures.fn (ctx a'.state a'.state.records c' i', b'.state.records, ())) with
        | cons n ns => rfl
        | nil => exact hb
    | .inr (.inl (j, ())), .inr (.inl (j', ())), ⟨hj, _⟩ => exact ⟨ha1, hj⟩

theorem runCommand_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {a a' : Acc v} (ha : AccRen R a a')
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c c' : (Ty.origin v.caller).den0}
    (hc : Ty.rel0 R.ctr (Ty.origin v.caller) c c') {i i' : x.input.den0}
    (hi : Ty.rel0 R.ctr x.input i i')
    {f f' : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))} (hf : Fun.Rel R.ctr f f') :
    ExRen R (runCommand T a x c i f) (runCommand T a' x c' i' f') := by
  have he := execCommand_ren ho hmo ha hx hc hi
  unfold runCommand
  revert he
  generalize execCommand T a x c i = y
  generalize execCommand T a' x c' i' = y'
  intro he
  match y, y', he with
  | .error _, .error _, h => exact h
  | .ok (.invalid _), .ok (.invalid _), h => subst h; rfl
  | .ok (.accepted b), .ok (.accepted b'), hb =>
    exact applyEvents_ren ho hmo (hf (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) hb
  | .ok (.rejected b j), .ok (.rejected b' j'), ⟨hb, hj⟩ =>
    exact applyEvents_ren ho hmo (hf (.inr (.inl (j, ())), ()) (.inr (.inl (j', ())), ()) ⟨⟨hj, trivial⟩, trivial⟩) hb

theorem execQuery_ren (ho : Ordered T v) {s s' : State v} (hs : StateRen R s s') {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 R.ctr (Ty.origin v.caller) c c')
    {i i' : x.input.den0} (hi : Ty.rel0 R.ctr x.input i i') :
    match execQuery s x c i, execQuery s' x c' i' with
    | .error rs, .error rs' => rs = rs'
    | .ok o, .ok o' => Ty.rel0 R.ctr x.output o o'
    | _, _ => False := by
  obtain ⟨hcl, hacc, hres⟩ := (ho.equi.self R.ctr).queries x hx
  unfold execQuery
  rw [admit_rel ho.equi hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => rfl
  | nil =>
    exact hres (queryCtx s s.records c i, ()) (queryCtx s' s'.records c' i', ())
      ⟨⟨hs.1, hi, hc, hs.2.2.2.1, trivial⟩, trivial⟩

theorem runQuery_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {a a' : Acc v} (ha : AccRen R a a') {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 R.ctr (Ty.origin v.caller) c c')
    {i i' : x.input.den0} (hi : Ty.rel0 R.ctr x.input i i')
    {f f' : Fun (Ty.fn [x.output] (.list v.event))} (hf : Fun.Rel R.ctr f f') :
    ExRen R (runQuery T a x c i f) (runQuery T a' x c' i' f') := by
  have he := execQuery_ren ho ha.1 hx hc hi
  unfold runQuery
  revert he
  generalize execQuery a.state x c i = y
  generalize execQuery a'.state x c' i' = y'
  intro he
  obtain ⟨⟨hrec, hmach, hpend, hnow, hfr, hn⟩, hevs0, hout, hown⟩ := ha
  match y, y', he with
  | .error _, .error _, h => subst h; rfl
  | .ok o, .ok o', ho' =>
    exact applyEvents_ren ho hmo (hf (o, ()) (o', ()) ⟨ho', trivial⟩)
      ⟨⟨hrec, hmach, hpend, hnow, from_succ hfr, hn⟩, hevs0, hout, hown⟩

theorem runOwn_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {a a' : Acc v} (ha : AccRen R a a') {eff eff' : OwnEffectV v.event}
    (he : OwnEffectV.Rel R.ctr eff eff') : ExRen R (runOwn T a eff) (runOwn T a' eff') := by
  cases he with
  | command name c i j hval hf =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    generalize hox : ownCommand (v := v) name i j = ox
    cases oc with
    | none => trivial
    | some hcp =>
      cases ox with
      | none => trivial
      | some x =>
        obtain ⟨hcp⟩ := hcp
        have hmem := ownCommand_mem hox
        obtain ⟨x, hi, hj⟩ := x
        subst hcp hi hj
        exact runCommand_ren ho hmo ha hmem rel0_own hval hf
  | query name c i o hval hf =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    generalize hox : ownQuery (v := v) name i o = ox
    cases oc with
    | none => trivial
    | some hcp =>
      cases ox with
      | none => trivial
      | some x =>
        obtain ⟨hcp⟩ := hcp
        have hmem := ownQuery_mem hox
        obtain ⟨x, hi, ho'⟩ := x
        subst hcp hi ho'
        exact runQuery_ren ho hmo ha hmem rel0_own hval hf

theorem settle_ren (ho : Ordered T v) (hmo : R.ctr.Mono) : (fuel : Nat) → {a a' : Acc v} → AccRen R a a' →
    ExRen R (settle T fuel a) (settle T fuel a')
  | fuel, a, a', ha => by
    have hown := ha.2.2.2
    unfold settle
    match h1 : a.own, h2 : a'.own, fuel, hown with
    | [], [], _, _ => exact ha
    | _ :: _, _ :: _, 0, _ => trivial
    | eff :: rest, eff' :: rest', f + 1, ⟨he, hr⟩ =>
      dsimp only
      obtain ⟨hst, hevs, hout, -⟩ := ha
      exact (runOwn_ren ho hmo (a := { a with own := rest }) (a' := { a' with own := rest' }) ⟨hst, hevs, hout, hr⟩
        he).bind fun b b' hb => settle_ren ho hmo f hb
    | [], _ :: _, _, h | _ :: _, [], _, h => exact h.elim

theorem machineInvariants_ren {records records' : v.records.den0}
    (hrec : Ty.rel0 R.ctr v.records records records') {now now' : Int}
    (hnow : R.ctr.point .ms now now') : {ms : List (MachineV v.records v.event)} → (∀ m ∈ ms, m.Equi) →
    {l l' : Machines ms} → Machines.Ren R.ctr l l' →
    (l.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        broken (m.invariants.fn (.inl (i.key, i.state, records, now, ()), ()))) =
      (l'.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        broken (m.invariants.fn (.inl (i.key, i.state, records', now', ()), ())))
  | [], _, .nil, .nil, _ => rfl
  | m :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    rw [machineInvariants_ren hrec hnow (fun m' h => hms m' (List.mem_cons_of_mem _ h)) hr]
    refine congrArg (· ++ _) (forall2_flatMap (fun i i' h => ?_) hi)
    exact broken_rel (((hms m List.mem_cons_self).self R.ctr).invariants _ _
      ⟨⟨h.1, h.2, hrec, hnow, trivial⟩, trivial⟩)

theorem invariants_ren (ho : Ordered T v) {s s' : State v} (hs : StateRen R s s') :
    invariants s = invariants s' := by
  obtain ⟨hrec, hmach, -, hnow, -, -⟩ := hs
  unfold invariants
  rw [machineInvariants_ren hrec hnow ho.equi.machines hmach]
  exact congrArg (· ++ _) (broken_rel ((ho.equi.self R.ctr).invariants _ _ ⟨hrec, trivial⟩))

/-- Outcomes related by `R`: the same fault on both sides, or the same outcome with related values. -/
def Outcome.Ren (R : Ren) : Outcome → Outcome → Prop
  | .accepted, .accepted => True
  | .answered w, .answered w' => WireVal.Rel R.ctr w w'
  | .rejected w, .rejected w' => WireVal.Rel R.ctr w w'
  | .invalid rs, .invalid rs' => rs = rs'
  | .fault f, .fault f' => f = f'
  | _, _ => False

/-- Results related by `R`, item by item. -/
def ResultRen (R : Ren) (r r' : Result v) : Prop :=
  StateRen R r.state r'.state ∧ Outcome.Ren R r.outcome r'.outcome ∧
    Forall2 (Ty.rel0 R.ctr v.event) r.events r'.events ∧ Forall2 (OutLine.Rel R) r.out r'.out

theorem finish_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {s0 s0' : State v} (hs0 : StateRen R s0 s0') {a a' : Except Fault (Acc v)}
    (ha : ExRen R a a') {o o' : Outcome} (hoo : Outcome.Ren R o o') :
    ResultRen R (finish T s0 a o) (finish T s0' a' o') := by
  have h := ha.bind fun b b' hb => settle_ren ho hmo v.cascadeNat hb
  unfold finish
  revert h
  generalize a >>= settle T v.cascadeNat = y
  generalize a' >>= settle T v.cascadeNat = y'
  intro h
  match y, y', h with
  | .error _, .error _, h => exact ⟨hs0, h, trivial, trivial⟩
  | .ok b, .ok b', hb =>
    dsimp only
    rw [invariants_ren ho hb.1]
    cases invariants b'.state with
    | cons n ns => exact ⟨hs0, rfl, trivial, trivial⟩
    | nil => exact ⟨hb.1, hoo, hb.2.1, hb.2.2.1⟩

section Fire
variable {r e : Ty}

theorem hitsAt_ren {m : MachineV r e} (hm : m.Equi) {records records' : r.den0}
    (hrec : Ty.rel0 R.ctr r records records') {dl dl' : Int} (hdl : R.ctr.point .ms dl dl')
    {i i' : Instance m} (hi : Instance.Rel R.ctr i i') : hitsAt records dl i = hitsAt records' dl' i' := by
  have ht := timerAt_rel hm hrec hi.1 hi.2
  unfold hitsAt timerOf
  revert ht
  generalize m.timerAt records i.key i.state = a
  generalize m.timerAt records' i'.key i'.state = b
  intro ht
  cases ht with
  | none => rfl
  | @some a b hab =>
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    exact decide_eq_decide.2 (PBij.point_ms_iff hab.1 hdl).1

theorem fireFirst_ren {m : MachineV r e} (hm : m.Equi) {records records' : r.den0}
    (hrec : Ty.rel0 R.ctr r records records') {now now' : Int} (hnow : R.ctr.point .ms now now')
    {dl dl' : Int} (hdl : R.ctr.point .ms dl dl') : {l l' : List (Instance m)} → Insts.Ren R.ctr l l' →
    Insts.Ren R.ctr (fireFirst m records now dl l).1 (fireFirst m records' now' dl' l').1 ∧
      Forall2 (Started.Rel R.ctr) (fireFirst m records now dl l).2.1
        (fireFirst m records' now' dl' l').2.1 ∧
      (fireFirst m records now dl l).2.2 = (fireFirst m records' now' dl' l').2.2
  | [], [], _ => ⟨trivial, trivial, rfl⟩
  | i :: is, i' :: is', ⟨hi, h⟩ => by
    have ih := fireFirst_ren hm hrec hnow hdl h
    have hhit := hitsAt_ren hm hrec hdl hi
    have hfired : Reacted.Rel R.ctr (fired m records now i) (fired m records' now' i') := by
      have ht := timerAt_rel hm hrec hi.1 hi.2
      unfold fired timerOf
      revert ht
      generalize m.timerAt records i.key i.state = a
      generalize m.timerAt records' i'.key i'.state = b
      intro ht
      cases ht with
      | none => exact ⟨hi, trivial⟩
      | some hab => exact enter_rel hm hrec hnow hi.1 hab.2
    simp only [fireFirst, hhit]
    split
    · exact ⟨⟨hfired.1, h⟩, hfired.2, rfl⟩
    · exact ⟨⟨hi, ih.1⟩, ih.2.1, ih.2.2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem fireMachines_ren {records records' : r.den0} (hrec : Ty.rel0 R.ctr r records records')
    {now now' : Int} (hnow : R.ctr.point .ms now now') {dl dl' : Int}
    (hdl : R.ctr.point .ms dl dl') :
    (done : Bool) → {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi) → {l l' : Machines ms} → Machines.Ren R.ctr l l' →
    Machines.Ren R.ctr (fireMachines records now dl done l).1 (fireMachines records' now' dl' done l').1 ∧
      Forall2 (Started.Rel R.ctr) (fireMachines records now dl done l).2.1
        (fireMachines records' now' dl' done l').2.1 ∧
      (fireMachines records now dl done l).2.2 = (fireMachines records' now' dl' done l').2.2
  | _, [], _, .nil, .nil, _ => ⟨trivial, trivial, rfl⟩
  | true, _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    have ih := fireMachines_ren hrec hnow hdl true (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    exact ⟨⟨hi, ih.1⟩, ih.2.1, rfl⟩
  | false, m :: _, hms, .cons l _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    have hy := fireFirst_ren (hms _ List.mem_cons_self) hrec hnow hdl hi
    simp only [fireMachines]
    rw [← hy.2.2]
    have ih := fireMachines_ren hrec hnow hdl (fireFirst m records now dl l).2.2
      (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    exact ⟨⟨hy.1, ih.1⟩, forall2_append hy.2.1 ih.2.1, ih.2.2⟩

theorem dues_ren {records records' : r.den0} (hrec : Ty.rel0 R.ctr r records records') {now now' : Int}
    (hnow : R.ctr.point .ms now now') : {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi) →
    {l l' : Machines ms} → Machines.Ren R.ctr l l' →
    Forall2 (R.ctr.point .ms) (dues records l.toSigma now) (dues records' l'.toSigma now')
  | [], _, .nil, .nil, _ => trivial
  | m :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    unfold dues
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    have ih := dues_ren hrec hnow (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    unfold dues at ih
    refine forall2_append (forall2_filterMap (fun i i' h => ?_) hi) ih
    have ht := timerAt_rel (hms m List.mem_cons_self) hrec h.1 h.2
    unfold timerOf
    revert ht
    generalize m.timerAt records i.key i.state = a
    generalize m.timerAt records' i'.key i'.state = b
    intro ht
    cases ht with
    | none => exact .none
    | @some a b hab =>
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only [Option.bind_some]
      have hle := (PBij.point_ms_iff hab.1 hnow).2.1
      by_cases h1 : a1 ≤ now
      · have h2 : b1 ≤ now' := hle.1 h1
        simp only [h1, h2, ↓reduceIte]; exact .some hab.1
      · have h2 : ¬ b1 ≤ now' := fun h2 => h1 (hle.2 h2)
        simp only [h1, h2, ↓reduceIte]; exact .none

end Fire

/-- The earliest of instants related one by one by a shift are related by it. -/
theorem min?_ren {R : PBij} : {l l' : List Int} → Forall2 (R.point .ms) l l' → Option.Rel (R.point .ms) l.min? l'.min?
  | [], [], _ => .none
  | a :: l, a' :: l', ⟨ha, h⟩ => by
    rw [List.min?_cons', List.min?_cons']
    refine .some ?_
    suffices ∀ {x x'} {l : List Int} {l' : List Int}, R.point .ms x x' → Forall2 (R.point .ms) l l' →
        R.point .ms (l.foldl min x) (l'.foldl min x') from this ha h
    intro x x' l l' hx hl
    induction l generalizing x x' l' with
    | nil => cases l' with
      | nil => exact hx
      | cons => exact hl.elim
    | cons b l ih =>
      cases l' with
      | nil => exact hl.elim
      | cons b' l' =>
        obtain ⟨hb, hl⟩ := hl
        simp only [List.foldl]
        refine ih (PBij.point_ms_of ?_) hl
        rw [PBij.point_ms_eq hx, PBij.point_ms_eq hb]
        simp only [Int.min_def]; split <;> split <;> omega
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem fire_ren (ho : Ordered T v) (hmo : R.ctr.Mono) : (fuel : Nat) → {s s' : State v} → StateRen R s s' →
    Option.Rel (fun x y => StateRen R x.1 y.1 ∧ Forall2 (Started.Rel R.ctr) x.2 y.2) (fire s fuel)
      (fire s' fuel)
  | 0, _, _, _ => .none
  | fuel + 1, s, s', hs => by
    unfold fire
    have hm := min?_ren (dues_ren hs.1 hs.2.2.2.1 ho.equi.machines hs.2.1)
    revert hm
    generalize (dues s.records s.machines.toSigma s.now).min? = a
    generalize (dues s'.records s'.machines.toSigma s'.now).min? = b
    intro hm
    cases hm with
    | none => exact .some ⟨hs, trivial⟩
    | @some dl dl' hdl =>
      dsimp only
      have hx := fireMachines_ren hs.1 hs.2.2.2.1 hdl false ho.equi.machines hs.2.1
      obtain ⟨hrec, -, hpend, hnow, hf, hn⟩ := hs
      have ih := fire_ren ho hmo fuel (s := { s with machines := (fireMachines s.records s.now dl false s.machines).1 })
        (s' := { s' with machines := (fireMachines s'.records s'.now dl' false s'.machines).1 })
        ⟨hrec, hx.1, hpend, hnow, hf, hn⟩
      revert ih
      generalize fire _ fuel = p
      generalize fire _ fuel = q
      intro ih
      cases ih with
      | none => exact .none
      | some h => exact .some ⟨h.1, forall2_append hx.2.1 h.2⟩

/-- Inputs related by `R`: an answer names the pending request `R` relates. -/
inductive Input.Ren (R : Ren) : Input v → Input v → Prop
  | command (i : Fin v.commands.length) {c c' : v.caller.den0} {x x' : (v.commands.get i).input.den0} :
      Ty.rel0 R.ctr v.caller c c' → Ty.rel0 R.ctr _ x x' →
      Input.Ren R (.command i c x) (.command i c' x')
  | query (i : Fin v.queries.length) {c c' : v.caller.den0} {x x' : (v.queries.get i).input.den0} :
      Ty.rel0 R.ctr v.caller c c' → Ty.rel0 R.ctr _ x x' →
      Input.Ren R (.query i c x) (.query i c' x')
  | answer {to to' : Nat} {w w' : WireVal} : R.wire.rel to to' → WireVal.Rel R.ctr w w' →
      Input.Ren R (.answer to w) (.answer to' w')
  | event (i : Fin v.subscribes.length) {x x' : (v.subscribes.get i).event.den0} :
      Ty.rel0 R.ctr _ x x' → Input.Ren R (.event i x) (.event i x')
  | clock {t t' : Int} : R.ctr.point .ms t t' → Input.Ren R (.clock t) (.clock t')

theorem answer_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {s s' : State v} (hs : StateRen R s s') {to to' : Nat}
    (hto : R.wire.rel to to') {t : Ty} {x x' : t.den0}
    (hx : Ty.rel0 R.ctr t x x') :
    ResultRen R (step T v s (.answer to ⟨t, x⟩)) (step T v s' (.answer to' ⟨t, x'⟩)) := by
  have hf := forall2_find? (p := (·.id == to)) (q := (·.id == to')) (fun _ _ h => PBij.rel_beq h.1 hto) hs.2.2.1
  simp only [step]
  revert hf
  generalize s.pending.find? _ = a
  generalize s'.pending.find? _ = b
  intro hf
  cases hf with
  | none => exact ⟨hs, rfl, trivial, trivial⟩
  | @some p p' hp =>
    obtain ⟨pid, psnd, pext, preq⟩ := p
    obtain ⟨pid', psnd', pext', preq'⟩ := p'
    obtain ⟨-, -, -, hrq⟩ := hp
    cases hrq with
    | @mk name input output rejection value value' holds holds' onAnswer onAnswer' hval hholds hon =>
      dsimp only
      cases Ty.same t (answerTy output rejection) with
      | none => exact ⟨hs, rfl, trivial, trivial⟩
      | some e =>
        obtain ⟨e⟩ := e
        subst e
        dsimp only
        have hb : broken (RequestV.holds ⟨name, input, output, rejection, value, holds, onAnswer⟩ x) =
            broken (RequestV.holds ⟨name, input, output, rejection, value', holds', onAnswer'⟩ x') := by
          unfold RequestV.holds
          cases hholds with
          | none => rfl
          | some hh => exact broken_rel (hh (value, x, ()) (value', x', ()) ⟨hval, hx, trivial⟩)
        rw [hb]
        cases broken (RequestV.holds ⟨name, input, output, rejection, value', holds', onAnswer'⟩ x') with
        | cons r rs => exact ⟨hs, rfl, trivial, trivial⟩
        | nil =>
          dsimp only
          obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
          refine finish_ren ho hmo ⟨hrec, hmach, hpend, hnow, hfr, hn⟩
            (applyEvents_ren ho hmo (hon (x, ()) (x', ()) ⟨hx, trivial⟩)
              (AccRen.ofState (s := { s with pending := s.pending.filter (·.id != to) })
                (s' := { s' with pending := s'.pending.filter (·.id != to') }) ⟨hrec, hmach, ?_, hnow, hfr, hn⟩))
            (o := .accepted) (o' := .accepted) trivial
          exact forall2_filter (fun _ _ h => by simp only [bne, PBij.rel_beq h.1 hto]) hpend

/-- The step reads no bag's or table's order, no name of its counters or wire ids beyond their order, and no origin of
time: from states related by a renaming that keeps the counters' order, on related inputs, it steps to related
results, item by item. -/
theorem step_ren (ho : Ordered T v) (hmo : R.ctr.Mono) {s s' : State v} (hs : StateRen R s s') {x x' : Input v}
    (hx : Input.Ren R x x') : ResultRen R (step T v s x) (step T v s' x') := by
  cases hx with
  | command i hc hi =>
    obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
    have hs1 : StateRen R { s with fresh := s.fresh + 1 } { s' with fresh := s'.fresh + 1 } :=
      ⟨hrec, hmach, hpend, hnow, from_succ hfr, hn⟩
    have he := execCommand_ren ho hmo (AccRen.ofState ⟨hrec, hmach, hpend, hnow, hfr, hn⟩) (List.get_mem _ _)
      (rel0_outside hc) hi
    simp only [step]
    revert he
    generalize execCommand T _ _ _ _ = y
    generalize execCommand T _ _ _ _ = y'
    intro he
    match y, y', he with
    | .error _, .error _, h => exact ⟨hs1, h, trivial, trivial⟩
    | .ok (.invalid _), .ok (.invalid _), h => exact ⟨hs1, h, trivial, trivial⟩
    | .ok (.rejected _ _), .ok (.rejected _ _), ⟨_, hj⟩ => exact ⟨hs1, .mk hj, trivial, trivial⟩
    | .ok (.accepted _), .ok (.accepted _), hb => exact finish_ren ho hmo hs1 (a := .ok _) (a' := .ok _) hb trivial
  | query i hc hi =>
    have he := execQuery_ren ho hs (List.get_mem _ _) (rel0_outside hc) hi
    simp only [step]
    revert he
    generalize execQuery s _ _ _ = y
    generalize execQuery s' _ _ _ = y'
    intro he
    match y, y', he with
    | .error _, .error _, h => exact ⟨hs, h, trivial, trivial⟩
    | .ok _, .ok _, h => exact ⟨hs, .mk h, trivial, trivial⟩
  | answer hto hw =>
    cases hw with
    | mk hx => exact answer_ren ho hmo hs hto hx
  | @event i y y' hx =>
    obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
    simp only [step]
    exact finish_ren ho hmo ⟨hrec, hmach, hpend, hnow, hfr, hn⟩
      (applyEvents_ren ho hmo (evs := [_]) (evs' := [_])
        ⟨(ho.equi.self R.ctr).subscribes _ (List.get_mem _ _) (y, ()) (y', ()) ⟨hx, trivial⟩, trivial⟩
        (AccRen.ofState ⟨hrec, hmach, hpend, hnow, hfr, hn⟩)) (o := .accepted) (o' := .accepted) trivial
  | @clock t t' ht =>
    simp only [step]
    have hlt := (PBij.point_ms_iff ht hs.2.2.2.1).2.2
    by_cases h : t < s.now
    · have h' : t' < s'.now := hlt.1 h
      simp only [h, h', ↓reduceIte]
      exact ⟨hs, rfl, trivial, trivial⟩
    · have h' : ¬ t' < s'.now := fun h' => h (hlt.2 h')
      simp only [h, h', ↓reduceIte]
      have hf := fire_ren ho hmo (v.cascadeNat + 1) (s := { s with now := t }) (s' := { s' with now := t' })
        ⟨hs.1, hs.2.1, hs.2.2.1, ht, hs.2.2.2.2⟩
      revert hf
      generalize fire _ _ = p
      generalize fire _ _ = q
      intro hf
      cases hf with
      | none => exact ⟨hs, rfl, trivial, trivial⟩
      | some h =>
        exact finish_ren ho hmo hs (start_ren h.2 (AccRen.ofState h.1)) trivial

end Step

end Tazuna.Ir
