import Tazuna.Semantics.StepRename
import Tazuna.Semantics.ShiftOrder

/-! The step does not read the order a bag or table is stored in, nor where time starts. Two states are the same up to
that order and a time shift `d` when their records relate under the renaming that keeps every name and moves every
instant by `d` (`Ty.rel0 (PBij.shifted d)`: bags and tables as multisets, instants moved, everything else equal), the
second's time is the first's moved by `d`, and every other part relates item by item, in the same order: instances,
pending requests, waiting own effects, events and out lines (`StateShift`). Stepping such states on such inputs gives
such results (`step_shift`); with no shift that is `step_same`. No spec can write an instant, so a step can only move
and compare the instants it is given, and moving them all alike changes no outcome (Lamport, "Real-Time Model Checking
is Really Simple", 2005). `StepRename` relates the collections only as multisets, since renaming fresh ids reorders
keys; with every name kept, the canonical order of instance keys (`machineStep`) is the same on both sides, a time
shift included (`Ty.cmp_shift`), so every effect starts, every own command runs and every wire id is given in the same
order. -/

namespace Tazuna.Ir

/-- The renaming that keeps every counter and moves every instant by `d` milliseconds, or keeps them when `d` is
none. -/
def PBij.shifted (d : Option Int) : PBij := { PBij.refl with shift := d }

theorem PBij.shifted_rel {d : Option Int} {a b : Nat} (h : (PBij.shifted d).rel a b) : a = b := h

/-- The renaming that keeps every counter and every wire id and moves every instant by `d`. -/
def Ren.shifted (d : Option Int) : Ren := ⟨PBij.shifted d, PBij.refl⟩

/-- The renaming that keeps every counter, every wire id and every instant. -/
abbrev Ren.refl : Ren := Ren.shifted none

/-- Values the same up to the order their bags and tables are stored in. -/
abbrev Ty.Same (t : Ty) : t.den0 → t.den0 → Prop := Ty.rel0 PBij.refl t

theorem Ty.same_of_deq {t : Ty} (hc : t.comparable = true) {x y : t.den0} (h : t.deq0 x y = true) : Ty.Same t x y :=
  Ty.rel0_deq_right hc (Ty.rel0_refl t hc x) h

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

/-- Values the same up to order and a time shift, put in the canonical order, relate item by item: items of one
Erlang term may change places, and the shift keeps the order (`Ty.cmp_shift`). -/
theorem Ty.sortBy_shift (T : List TypeDecl) {d : Option Int} {t : Ty} (hc : t.comparable = true)
    (ho : t.ordered T = true) {xs ys : List t.den0} (h : Multi (Ty.rel0 (PBij.shifted d) t) xs ys) :
    Forall2 (Ty.rel0 (PBij.shifted d) t) (Ty.sortBy T t xs) (Ty.sortBy T t ys) := by
  obtain ⟨zs, hz, hp⟩ := h
  have h1 : Forall2 (Ty.rel0 (PBij.shifted d) t) (Ty.sortBy T t xs) (Ty.sortBy T t zs) :=
    forall2_mergeSort hz fun a b a' b' ha hb => by
      show (Erl.cmp _ _).isLE = (Erl.cmp _ _).isLE
      rw [Ty.cmp_shift T PBij.shifted_rel t ho ha hb]
  have hsort : ∀ l : List t.den0, (Ty.sortBy T t l).map (Ty.erl T t) = Erl.sort (l.map (Ty.erl T t)) := fun l => by
    unfold Ty.sortBy Erl.sort
    exact List.map_mergeSort (fun _ _ _ _ => rfl)
  have h2 : (Ty.sortBy T t zs).map (Ty.erl T t) = (Ty.sortBy T t ys).map (Ty.erl T t) := by
    rw [hsort, hsort]; exact (Erl.sort_eq_iff _ _).2 (hp.map _)
  exact forall2_imp (fun _ _ ⟨_, h, e⟩ => Ty.rel0_deq_right hc h ((Ty.erl_iff T t ho _ _).2 e))
    (forall2_comp h1 (forall2_of_map_eq h2))

namespace Step

section Machine
variable {r e : Ty} {d : Option Int}

/-- Instances the same up to order and a time shift, item by item. -/
abbrev Insts.Shift (d : Option Int) {m : MachineV r e} : List (Instance m) → List (Instance m) → Prop :=
  Forall2 (Instance.Rel (PBij.shifted d))

def Machines.Shift (d : Option Int) : {ms : List (MachineV r e)} → Machines ms → Machines ms → Prop
  | _, .nil, .nil => True
  | _, .cons l rest, .cons l' rest' => Insts.Shift d l l' ∧ Machines.Shift d rest rest'

/-- Instances the same up to order, item by item. -/
abbrev Machines.Same {ms : List (MachineV r e)} : Machines ms → Machines ms → Prop := Machines.Shift none

theorem reactKey_shift {m : MachineV r e} (hm : m.Equi) {insts insts' : List (Instance m)}
    (hl : Insts.Shift d insts insts') {records records' : r.den0} (hrec : Ty.rel0 (PBij.shifted d) r records records')
    {now now' : Int} (hnow : (PBij.shifted d).point .ms now now') {ev ev' : e.den0}
    (hev : Ty.rel0 (PBij.shifted d) e ev ev') {k k' : m.key.den0} (hk : Ty.rel0 (PBij.shifted d) m.key k k') :
    Reacted.Rel (PBij.shifted d) (reactKey m insts records now ev k) (reactKey m insts' records' now' ev' k') := by
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
    have hon := (hm.self (PBij.shifted d)).on (.inl (i.key, i.state, records, now, ()), ev, ())
      (.inl (i'.key, i'.state, records', now', ()), ev', ()) ⟨⟨hi.1, hi.2, hrec, hnow, trivial⟩, hev, trivial⟩
    revert hon
    generalize m.on.fn (.inl (i.key, i.state, records, now, ()), ev, ()) = x
    generalize m.on.fn (.inl (i'.key, i'.state, records', now', ()), ev', ()) = y
    intro hon
    match x, y, hon with
    | .inr (.inl (s, ())), .inr (.inl (s', ())), ⟨hs, _⟩ => exact enter_rel hm hrec hnow hi.1 hs
    | .inl (), .inl (), _ => exact ⟨hi, trivial⟩

theorem machineStep_shift (T : List TypeDecl) {m : MachineV r e} (hm : m.Equi) (ho : m.key.ordered T = true)
    {records records' : r.den0} (hrec : Ty.rel0 (PBij.shifted d) r records records') {now now' : Int}
    (hnow : (PBij.shifted d).point .ms now now') {ev ev' : e.den0} (hev : Ty.rel0 (PBij.shifted d) e ev ev')
    {insts insts' : List (Instance m)} (hl : Insts.Shift d insts insts') :
    Insts.Shift d (machineStep T records now ev m insts).1 (machineStep T records' now' ev' m insts').1 ∧
      Forall2 (Started.Rel (PBij.shifted d)) (machineStep T records now ev m insts).2
        (machineStep T records' now' ev' m insts').2 := by
  have hb : Multi (Ty.rel0 (PBij.shifted d) m.key) (m.instances.fn (records, ())) (m.instances.fn (records', ())) :=
    (hm.self (PBij.shifted d)).instances _ _ ⟨hrec, trivial⟩
  have hd : Multi (Ty.rel0 (PBij.shifted d) m.key) (dedupBy m.key.deq0 (m.instances.fn (records, ())))
      (dedupBy m.key.deq0 (m.instances.fn (records', ()))) := by
    obtain ⟨zs, h, hz⟩ := hb
    exact ((Multi.of_forall2 (forall2_dedupBy (f := m.key.deq0) (f' := m.key.deq0)
      (fun _ _ _ _ => Ty.rel0_deq m.key hm.key) h)).comp
      (dedupBy_perm_multi (Ty.canon_iff m.key hm.key) hz)).imp fun _ _ ⟨_, h1, h2⟩ => Ty.rel0_deq_right hm.key h1 h2
  have hr := forall2_map2 (r' := Reacted.Rel (PBij.shifted d)) (fun _ _ hk => reactKey_shift hm hl hrec hnow hev hk)
    (Ty.sortBy_shift T hm.key ho hd)
  exact ⟨forall2_map2 (fun _ _ h => h.1) hr, forall2_flatMap2 (fun _ _ h => h.2) hr⟩

theorem reactMachines_shift (T : List TypeDecl) {records records' : r.den0}
    (hrec : Ty.rel0 (PBij.shifted d) r records records') {now now' : Int} (hnow : (PBij.shifted d).point .ms now now')
    {ev ev' : e.den0} (hev : Ty.rel0 (PBij.shifted d) e ev ev') : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.Equi ∧ m.key.ordered T = true) → {l l' : Machines ms} → Machines.Shift d l l' →
    Machines.Shift d (reactMachines T records now ev l).1 (reactMachines T records' now' ev' l').1 ∧
      Forall2 (Started.Rel (PBij.shifted d)) (reactMachines T records now ev l).2
        (reactMachines T records' now' ev' l').2
  | [], _, .nil, .nil, _ => ⟨trivial, trivial⟩
  | _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hx, hrest⟩ := h
    have hm := hms _ List.mem_cons_self
    have h1 := machineStep_shift T hm.1 hm.2 hrec hnow hev hx
    have h2 := reactMachines_shift T hrec hnow hev (fun m h => hms m (List.mem_cons_of_mem _ h)) hrest
    simp only [reactMachines]
    exact ⟨⟨h1.1, h2.1⟩, forall2_append h1.2 h2.2⟩

end Machine

variable {v : ServiceV} {d : Option Int}

/-- States the same up to the order their bags and tables are stored in and the time shift `d`. -/
def StateShift (d : Option Int) (s s' : State v) : Prop :=
  Ty.rel0 (PBij.shifted d) v.records s.records s'.records ∧ Machines.Shift d s.machines s'.machines ∧
    Forall2 (Pending.Rel (Ren.shifted d)) s.pending s'.pending ∧ (PBij.shifted d).point .ms s.now s'.now ∧
    s.fresh = s'.fresh ∧ s.nextId = s'.nextId

/-- States the same up to the order their bags and tables are stored in. -/
abbrev StateSame (s s' : State v) : Prop := StateShift none s s'

/-- Steps in progress the same up to that order and that shift. -/
def AccShift (d : Option Int) (a a' : Acc v) : Prop :=
  StateShift d a.state a'.state ∧ Forall2 (Ty.rel0 (PBij.shifted d) v.event) a.events a'.events ∧
    Forall2 (OutLine.Rel (Ren.shifted d)) a.out a'.out ∧ Forall2 (OwnEffectV.Rel (PBij.shifted d)) a.own a'.own

/-- What runs from such steps end in: a fault on both sides, or such steps. -/
def ExShift (d : Option Int) : Except Fault (Acc v) → Except Fault (Acc v) → Prop
  | .error _, .error _ => True
  | .ok a, .ok a' => AccShift d a a'
  | _, _ => False

theorem AccShift.ofState {s s' : State v} (h : StateShift d s s') :
    AccShift d ({ state := s } : Acc v) { state := s' } :=
  ⟨h, trivial, trivial, trivial⟩

theorem ExShift.bind {x x' : Except Fault (Acc v)} (h : ExShift d x x') {f g : Acc v → Except Fault (Acc v)}
    (hfg : ∀ b b', AccShift d b b' → ExShift d (f b) (g b')) : ExShift d (x >>= f) (x' >>= g) := by
  match x, x', h with
  | .error _, .error _, _ => trivial
  | .ok b, .ok b', h => exact hfg b b' h

/-- The machines and reactions with their functions respecting every renaming, and keys in a canonical order. -/
structure Ordered (T : List TypeDecl) (v : ServiceV) : Prop where
  equi : v.Equivariant
  keys : ∀ m ∈ v.machines, m.key.ordered T = true

variable {T : List TypeDecl}

theorem react_shift (ho : Ordered T v) {s s' : State v} (hs : StateShift d s s') {ev ev' : v.event.den0}
    (hev : Ty.rel0 (PBij.shifted d) v.event ev ev') :
    StateShift d (react T s ev).1 (react T s' ev').1 ∧
      Forall2 (Started.Rel (PBij.shifted d)) (react T s ev).2 (react T s' ev').2 := by
  obtain ⟨hrec, hmach, hpend, hnow, hf, hn⟩ := hs
  have hrec' : Ty.rel0 (PBij.shifted d) v.records (v.apply.fn (.inl (s.records, s.now, ()), ev, ()))
      (v.apply.fn (.inl (s'.records, s'.now, ()), ev', ())) :=
    (ho.equi.self (PBij.shifted d)).apply _ _ ⟨⟨hrec, hnow, trivial⟩, hev, trivial⟩
  have hm := reactMachines_shift T hrec' hnow hev (fun m hm => ⟨ho.equi.machines m hm, ho.keys m hm⟩) hmach
  unfold react
  dsimp only
  refine ⟨⟨hrec', hm.1, hpend, hnow, hf, hn⟩, forall2_append hm.2 ?_⟩
  have hx : ∀ x ∈ v.reactions, Forall2 (Started.Rel (PBij.shifted d))
      ((x.effectsAt ev (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) s.now).map (.reaction x.name, ·))
      ((x.effectsAt ev' (v.apply.fn (.inl (s'.records, s'.now, ()), ev', ())) s'.now).map (.reaction x.name, ·)) :=
    fun x hx => forall2_map2 (fun _ _ h => ⟨.reaction x.name, h⟩)
      (EffectFun.apply_rel x.react ((ho.equi.self (PBij.shifted d)).reactions x hx) ⟨⟨hrec', hnow, trivial⟩, hev, trivial⟩)
  clear hm hpend
  revert hx
  induction v.reactions with
  | nil => intro; trivial
  | cons x xs ih =>
    intro hx
    simp only [List.flatMap_cons]
    exact forall2_append (hx x List.mem_cons_self) (ih fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem start_shift : {effs effs' : List (Sender × EffectV v.event)} →
    Forall2 (Started.Rel (PBij.shifted d)) effs effs' → {a a' : Acc v} → AccShift d a a' →
    ExShift d (start a effs) (start a' effs')
  | [], [], _, _, _, ha => ha
  | (snd, eff) :: effs, (snd', eff') :: effs', ⟨⟨hs, he⟩, h⟩, a, a', ha => by
    unfold start
    rw [List.foldlM_cons, List.foldlM_cons]
    cases he with
    | @request r r' hrr =>
      dsimp only
      rw [← RequestV.ownerIn_rel hrr v.declared]
      cases r.ownerIn v.declared with
      | none => trivial
      | some x =>
        obtain ⟨⟨hrec, hmach, hpend, hnow, hf, hn⟩, hev, hout, hown⟩ := ha
        have hline : OutLine.Rel (Ren.shifted d) ⟨a.state.nextId, x, r.name, ⟨r.input, r.value⟩⟩
            ⟨a'.state.nextId, x, r'.name, ⟨r'.input, r'.value⟩⟩ := by
          cases hrr with
          | mk _ _ _ _ hv _ _ => exact ⟨hn, rfl, rfl, .mk hv⟩
        exact start_shift h ⟨⟨hrec, hmach, forall2_append hpend ⟨⟨hn, hs, rfl, hrr⟩, trivial⟩, hnow, hf,
          by simp only [hn]⟩, hev, forall2_append hout ⟨hline, trivial⟩, hown⟩
    | command name c i j hval hf =>
      obtain ⟨hst, hev, hout, hown⟩ := ha
      exact start_shift h ⟨hst, hev, hout, forall2_append hown ⟨.command _ _ _ _ hval hf, trivial⟩⟩
    | query name c i o hval hf =>
      obtain ⟨hst, hev, hout, hown⟩ := ha
      exact start_shift h ⟨hst, hev, hout, forall2_append hown ⟨.query _ _ _ _ hval hf, trivial⟩⟩
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

theorem applyEvents_shift (ho : Ordered T v) : {evs evs' : List v.event.den0} →
    Forall2 (Ty.rel0 (PBij.shifted d) v.event) evs evs' → {a a' : Acc v} → AccShift d a a' →
    ExShift d (applyEvents T a evs) (applyEvents T a' evs')
  | [], [], _, _, _, ha => ha
  | ev :: evs, ev' :: evs', ⟨hev, h⟩, a, a', ha => by
    unfold applyEvents
    rw [List.foldlM_cons, List.foldlM_cons]
    have hr := react_shift ho ha.1 hev
    obtain ⟨_, hevs, hout, hown⟩ := ha
    refine (start_shift hr.2 (a := { a with state := (react T a.state ev).1, events := a.events ++ [ev] })
      (a' := { a' with state := (react T a'.state ev').1, events := a'.events ++ [ev'] })
      ⟨hr.1, forall2_append hevs ⟨hev, trivial⟩, hout, hown⟩).bind fun b b' hb => ?_
    exact applyEvents_shift ho h hb
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

/-- What a command's runs from such steps end in. -/
def RanShift (d : Option Int) {j : Ty} : Except Fault (Ran v j) → Except Fault (Ran v j) → Prop
  | .error _, .error _ => True
  | .ok (.invalid rs), .ok (.invalid rs') => rs = rs'
  | .ok (.rejected a x), .ok (.rejected a' x') => AccShift d a a' ∧ Ty.rel0 (PBij.shifted d) j x x'
  | .ok (.accepted a), .ok (.accepted a') => AccShift d a a'
  | _, _ => False

theorem execCommand_shift (ho : Ordered T v) {a a' : Acc v} (ha : AccShift d a a')
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c c' : (Ty.origin v.caller).den0}
    (hc : Ty.rel0 (PBij.shifted d) (Ty.origin v.caller) c c') {i i' : x.input.den0}
    (hi : Ty.rel0 (PBij.shifted d) x.input i i') :
    RanShift d (execCommand T a x c i) (execCommand T a' x c' i') := by
  obtain ⟨hcl, hacc, hdec, hens⟩ := (ho.equi.self (PBij.shifted d)).commands x hx
  unfold execCommand
  rw [admit_rel ho.equi hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => rfl
  | nil =>
    dsimp only
    have hcx : Ty.rel0 (PBij.shifted d) (Ty.ctx v.records x.input v.caller) (ctx a.state a.state.records c i)
        (ctx a'.state a'.state.records c' i') := ⟨ha.1.1, hi, hc, ha.1.2.2.2.1, ha.1.2.2.2.2.1, trivial⟩
    have hd := hdec (ctx a.state a.state.records c i, ()) (ctx a'.state a'.state.records c' i', ()) ⟨hcx, trivial⟩
    revert hd
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = dc
    generalize x.decide.fn (ctx a'.state a'.state.records c' i', ()) = dc'
    intro hd
    obtain ⟨⟨hrec, hmach, hpend, hnow, hf, hn⟩, hevs0, hout, hown⟩ := ha
    have ha1 : AccShift d { a with state := { a.state with fresh := a.state.fresh + 1 } }
        { a' with state := { a'.state with fresh := a'.state.fresh + 1 } } :=
      ⟨⟨hrec, hmach, hpend, hnow, by simp only [hf], hn⟩, hevs0, hout, hown⟩
    match dc, dc', hd with
    | .inl (evs, ()), .inl (evs', ()), ⟨hevs, _⟩ =>
      dsimp only
      have he := applyEvents_shift ho hevs ha1
      revert he
      generalize applyEvents T _ evs = y
      generalize applyEvents T _ evs' = y'
      intro he
      match y, y', he with
      | .error _, .error _, _ => trivial
      | .ok b, .ok b', hb =>
        show RanShift d (match broken _ with | _ :: _ => _ | [] => _) (match broken _ with | _ :: _ => _ | [] => _)
        rw [broken_rel (hens (ctx a.state a.state.records c i, b.state.records, ())
          (ctx a'.state a'.state.records c' i', b'.state.records, ()) ⟨hcx, hb.1.1, trivial⟩)]
        cases broken (x.ensures.fn (ctx a'.state a'.state.records c' i', b'.state.records, ())) with
        | cons n ns => trivial
        | nil => exact hb
    | .inr (.inl (j, ())), .inr (.inl (j', ())), ⟨hj, _⟩ => exact ⟨ha1, hj⟩

theorem runCommand_shift (ho : Ordered T v) {a a' : Acc v} (ha : AccShift d a a')
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c c' : (Ty.origin v.caller).den0}
    (hc : Ty.rel0 (PBij.shifted d) (Ty.origin v.caller) c c') {i i' : x.input.den0}
    (hi : Ty.rel0 (PBij.shifted d) x.input i i')
    {f f' : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))} (hf : Fun.Rel (PBij.shifted d) f f') :
    ExShift d (runCommand T a x c i f) (runCommand T a' x c' i' f') := by
  have he := execCommand_shift ho ha hx hc hi
  unfold runCommand
  revert he
  generalize execCommand T a x c i = y
  generalize execCommand T a' x c' i' = y'
  intro he
  match y, y', he with
  | .error _, .error _, _ => trivial
  | .ok (.invalid _), .ok (.invalid _), _ => trivial
  | .ok (.accepted b), .ok (.accepted b'), hb =>
    exact applyEvents_shift ho (hf (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) hb
  | .ok (.rejected b j), .ok (.rejected b' j'), ⟨hb, hj⟩ =>
    exact applyEvents_shift ho (hf (.inr (.inl (j, ())), ()) (.inr (.inl (j', ())), ()) ⟨⟨hj, trivial⟩, trivial⟩) hb

theorem execQuery_shift (ho : Ordered T v) {s s' : State v} (hs : StateShift d s s') {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 (PBij.shifted d) (Ty.origin v.caller) c c')
    {i i' : x.input.den0} (hi : Ty.rel0 (PBij.shifted d) x.input i i') :
    match execQuery s x c i, execQuery s' x c' i' with
    | .error rs, .error rs' => rs = rs'
    | .ok o, .ok o' => Ty.rel0 (PBij.shifted d) x.output o o'
    | _, _ => False := by
  obtain ⟨hcl, hacc, hres⟩ := (ho.equi.self (PBij.shifted d)).queries x hx
  unfold execQuery
  rw [admit_rel ho.equi hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => rfl
  | nil =>
    exact hres (queryCtx s s.records c i, ()) (queryCtx s' s'.records c' i', ())
      ⟨⟨hs.1, hi, hc, hs.2.2.2.1, trivial⟩, trivial⟩

theorem runQuery_shift (ho : Ordered T v) {a a' : Acc v} (ha : AccShift d a a') {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 (PBij.shifted d) (Ty.origin v.caller) c c')
    {i i' : x.input.den0} (hi : Ty.rel0 (PBij.shifted d) x.input i i')
    {f f' : Fun (Ty.fn [x.output] (.list v.event))} (hf : Fun.Rel (PBij.shifted d) f f') :
    ExShift d (runQuery T a x c i f) (runQuery T a' x c' i' f') := by
  have he := execQuery_shift ho ha.1 hx hc hi
  unfold runQuery
  revert he
  generalize execQuery a.state x c i = y
  generalize execQuery a'.state x c' i' = y'
  intro he
  obtain ⟨⟨hrec, hmach, hpend, hnow, hfr, hn⟩, hevs0, hout, hown⟩ := ha
  match y, y', he with
  | .error _, .error _, _ => trivial
  | .ok o, .ok o', ho' =>
    exact applyEvents_shift ho (hf (o, ()) (o', ()) ⟨ho', trivial⟩)
      ⟨⟨hrec, hmach, hpend, hnow, by simp only [hfr], hn⟩, hevs0, hout, hown⟩

theorem runOwn_shift (ho : Ordered T v) {a a' : Acc v} (ha : AccShift d a a') {eff eff' : OwnEffectV v.event}
    (he : OwnEffectV.Rel (PBij.shifted d) eff eff') : ExShift d (runOwn T a eff) (runOwn T a' eff') := by
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
        exact runCommand_shift ho ha hmem rel0_own hval hf
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
        exact runQuery_shift ho ha hmem rel0_own hval hf

theorem settle_shift (ho : Ordered T v) : (fuel : Nat) → {a a' : Acc v} → AccShift d a a' →
    ExShift d (settle T fuel a) (settle T fuel a')
  | fuel, a, a', ha => by
    have hown := ha.2.2.2
    unfold settle
    match h1 : a.own, h2 : a'.own, fuel, hown with
    | [], [], _, _ => exact ha
    | _ :: _, _ :: _, 0, _ => trivial
    | eff :: rest, eff' :: rest', f + 1, ⟨he, hr⟩ =>
      dsimp only
      obtain ⟨hst, hevs, hout, -⟩ := ha
      exact (runOwn_shift ho (a := { a with own := rest }) (a' := { a' with own := rest' }) ⟨hst, hevs, hout, hr⟩
        he).bind fun b b' hb => settle_shift ho f hb
    | [], _ :: _, _, h | _ :: _, [], _, h => exact h.elim

theorem machineInvariants_shift {records records' : v.records.den0}
    (hrec : Ty.rel0 (PBij.shifted d) v.records records records') {now now' : Int}
    (hnow : (PBij.shifted d).point .ms now now') : {ms : List (MachineV v.records v.event)} → (∀ m ∈ ms, m.Equi) →
    {l l' : Machines ms} → Machines.Shift d l l' →
    (l.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        broken (m.invariants.fn (.inl (i.key, i.state, records, now, ()), ()))) =
      (l'.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        broken (m.invariants.fn (.inl (i.key, i.state, records', now', ()), ())))
  | [], _, .nil, .nil, _ => rfl
  | m :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    rw [machineInvariants_shift hrec hnow (fun m' h => hms m' (List.mem_cons_of_mem _ h)) hr]
    refine congrArg (· ++ _) (forall2_flatMap (fun i i' h => ?_) hi)
    exact broken_rel (((hms m List.mem_cons_self).self (PBij.shifted d)).invariants _ _
      ⟨⟨h.1, h.2, hrec, hnow, trivial⟩, trivial⟩)

theorem invariants_shift (ho : Ordered T v) {s s' : State v} (hs : StateShift d s s') :
    invariants s = invariants s' := by
  obtain ⟨hrec, hmach, -, hnow, -, -⟩ := hs
  unfold invariants
  rw [machineInvariants_shift hrec hnow ho.equi.machines hmach]
  exact congrArg (· ++ _) (broken_rel ((ho.equi.self (PBij.shifted d)).invariants _ _ ⟨hrec, trivial⟩))

/-- Outcomes the same up to order and a time shift: a fault on both sides, or the same outcome with related values. -/
def Outcome.Shift (d : Option Int) : Outcome → Outcome → Prop
  | .accepted, .accepted => True
  | .answered w, .answered w' => WireVal.Rel (PBij.shifted d) w w'
  | .rejected w, .rejected w' => WireVal.Rel (PBij.shifted d) w w'
  | .invalid rs, .invalid rs' => rs = rs'
  | .fault _, .fault _ => True
  | _, _ => False

/-- Outcomes the same up to order. -/
abbrev Outcome.Same : Outcome → Outcome → Prop := Outcome.Shift none

/-- Results the same up to order and a time shift. -/
def ResultShift (d : Option Int) (r r' : Result v) : Prop :=
  StateShift d r.state r'.state ∧ Outcome.Shift d r.outcome r'.outcome ∧
    Forall2 (Ty.rel0 (PBij.shifted d) v.event) r.events r'.events ∧ Forall2 (OutLine.Rel (Ren.shifted d)) r.out r'.out

/-- Results the same up to order. -/
abbrev ResultSame (r r' : Result v) : Prop := ResultShift none r r'

theorem finish_shift (ho : Ordered T v) {s0 s0' : State v} (hs0 : StateShift d s0 s0') {a a' : Except Fault (Acc v)}
    (ha : ExShift d a a') {o o' : Outcome} (hoo : Outcome.Shift d o o') :
    ResultShift d (finish T s0 a o) (finish T s0' a' o') := by
  have h := ha.bind fun b b' hb => settle_shift ho v.cascadeNat hb
  unfold finish
  revert h
  generalize a >>= settle T v.cascadeNat = y
  generalize a' >>= settle T v.cascadeNat = y'
  intro h
  match y, y', h with
  | .error _, .error _, _ => exact ⟨hs0, trivial, trivial, trivial⟩
  | .ok b, .ok b', hb =>
    dsimp only
    rw [invariants_shift ho hb.1]
    cases invariants b'.state with
    | cons n ns => exact ⟨hs0, trivial, trivial, trivial⟩
    | nil => exact ⟨hb.1, hoo, hb.2.1, hb.2.2.1⟩

section Fire
variable {r e : Ty}

theorem hitsAt_shift {m : MachineV r e} (hm : m.Equi) {records records' : r.den0}
    (hrec : Ty.rel0 (PBij.shifted d) r records records') {dl dl' : Int} (hdl : (PBij.shifted d).point .ms dl dl')
    {i i' : Instance m} (hi : Instance.Rel (PBij.shifted d) i i') : hitsAt records dl i = hitsAt records' dl' i' := by
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

theorem fireFirst_shift {m : MachineV r e} (hm : m.Equi) {records records' : r.den0}
    (hrec : Ty.rel0 (PBij.shifted d) r records records') {now now' : Int} (hnow : (PBij.shifted d).point .ms now now')
    {dl dl' : Int} (hdl : (PBij.shifted d).point .ms dl dl') : {l l' : List (Instance m)} → Insts.Shift d l l' →
    Insts.Shift d (fireFirst m records now dl l).1 (fireFirst m records' now' dl' l').1 ∧
      Forall2 (Started.Rel (PBij.shifted d)) (fireFirst m records now dl l).2.1
        (fireFirst m records' now' dl' l').2.1 ∧
      (fireFirst m records now dl l).2.2 = (fireFirst m records' now' dl' l').2.2
  | [], [], _ => ⟨trivial, trivial, rfl⟩
  | i :: is, i' :: is', ⟨hi, h⟩ => by
    have ih := fireFirst_shift hm hrec hnow hdl h
    have hhit := hitsAt_shift hm hrec hdl hi
    have hfired : Reacted.Rel (PBij.shifted d) (fired m records now i) (fired m records' now' i') := by
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

theorem fireMachines_shift {records records' : r.den0} (hrec : Ty.rel0 (PBij.shifted d) r records records')
    {now now' : Int} (hnow : (PBij.shifted d).point .ms now now') {dl dl' : Int}
    (hdl : (PBij.shifted d).point .ms dl dl') :
    (done : Bool) → {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi) → {l l' : Machines ms} → Machines.Shift d l l' →
    Machines.Shift d (fireMachines records now dl done l).1 (fireMachines records' now' dl' done l').1 ∧
      Forall2 (Started.Rel (PBij.shifted d)) (fireMachines records now dl done l).2.1
        (fireMachines records' now' dl' done l').2.1 ∧
      (fireMachines records now dl done l).2.2 = (fireMachines records' now' dl' done l').2.2
  | _, [], _, .nil, .nil, _ => ⟨trivial, trivial, rfl⟩
  | true, _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    have ih := fireMachines_shift hrec hnow hdl true (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    exact ⟨⟨hi, ih.1⟩, ih.2.1, rfl⟩
  | false, m :: _, hms, .cons l _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    have hy := fireFirst_shift (hms _ List.mem_cons_self) hrec hnow hdl hi
    simp only [fireMachines]
    rw [← hy.2.2]
    have ih := fireMachines_shift hrec hnow hdl (fireFirst m records now dl l).2.2
      (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    exact ⟨⟨hy.1, ih.1⟩, forall2_append hy.2.1 ih.2.1, ih.2.2⟩

theorem dues_shift {records records' : r.den0} (hrec : Ty.rel0 (PBij.shifted d) r records records') {now now' : Int}
    (hnow : (PBij.shifted d).point .ms now now') : {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi) →
    {l l' : Machines ms} → Machines.Shift d l l' →
    Forall2 ((PBij.shifted d).point .ms) (dues records l.toSigma now) (dues records' l'.toSigma now')
  | [], _, .nil, .nil, _ => trivial
  | m :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    unfold dues
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    have ih := dues_shift hrec hnow (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
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
theorem min?_shift {R : PBij} : {l l' : List Int} → Forall2 (R.point .ms) l l' → Option.Rel (R.point .ms) l.min? l'.min?
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

theorem fire_shift (ho : Ordered T v) : (fuel : Nat) → {s s' : State v} → StateShift d s s' →
    Option.Rel (fun x y => StateShift d x.1 y.1 ∧ Forall2 (Started.Rel (PBij.shifted d)) x.2 y.2) (fire s fuel)
      (fire s' fuel)
  | 0, _, _, _ => .none
  | fuel + 1, s, s', hs => by
    unfold fire
    have hm := min?_shift (dues_shift hs.1 hs.2.2.2.1 ho.equi.machines hs.2.1)
    revert hm
    generalize (dues s.records s.machines.toSigma s.now).min? = a
    generalize (dues s'.records s'.machines.toSigma s'.now).min? = b
    intro hm
    cases hm with
    | none => exact .some ⟨hs, trivial⟩
    | @some dl dl' hdl =>
      dsimp only
      have hx := fireMachines_shift hs.1 hs.2.2.2.1 hdl false ho.equi.machines hs.2.1
      obtain ⟨hrec, -, hpend, hnow, hf, hn⟩ := hs
      have ih := fire_shift ho fuel (s := { s with machines := (fireMachines s.records s.now dl false s.machines).1 })
        (s' := { s' with machines := (fireMachines s'.records s'.now dl' false s'.machines).1 })
        ⟨hrec, hx.1, hpend, hnow, hf, hn⟩
      revert ih
      generalize fire _ fuel = p
      generalize fire _ fuel = q
      intro ih
      cases ih with
      | none => exact .none
      | some h => exact .some ⟨h.1, forall2_append hx.2.1 h.2⟩

/-- Inputs the same up to the order of their values' bags and tables and the time shift `d`. -/
inductive Input.Shift (d : Option Int) : Input v → Input v → Prop
  | command (i : Fin v.commands.length) {c c' : v.caller.den0} {x x' : (v.commands.get i).input.den0} :
      Ty.rel0 (PBij.shifted d) v.caller c c' → Ty.rel0 (PBij.shifted d) _ x x' →
      Input.Shift d (.command i c x) (.command i c' x')
  | query (i : Fin v.queries.length) {c c' : v.caller.den0} {x x' : (v.queries.get i).input.den0} :
      Ty.rel0 (PBij.shifted d) v.caller c c' → Ty.rel0 (PBij.shifted d) _ x x' →
      Input.Shift d (.query i c x) (.query i c' x')
  | answer (to : Nat) {w w' : WireVal} : WireVal.Rel (PBij.shifted d) w w' →
      Input.Shift d (.answer to w) (.answer to w')
  | event (i : Fin v.subscribes.length) {x x' : (v.subscribes.get i).event.den0} :
      Ty.rel0 (PBij.shifted d) _ x x' → Input.Shift d (.event i x) (.event i x')
  | clock {t t' : Int} : (PBij.shifted d).point .ms t t' → Input.Shift d (.clock t) (.clock t')

/-- Inputs the same up to the order of their values' bags and tables. -/
abbrev Input.Same : Input v → Input v → Prop := Input.Shift none

theorem answer_shift (ho : Ordered T v) {s s' : State v} (hs : StateShift d s s') (to : Nat) {t : Ty} {x x' : t.den0}
    (hx : Ty.rel0 (PBij.shifted d) t x x') :
    ResultShift d (step T v s (.answer to ⟨t, x⟩)) (step T v s' (.answer to ⟨t, x'⟩)) := by
  have hf := forall2_find? (p := (·.id == to)) (q := (·.id == to)) (fun p q h => by
    have : p.id = q.id := h.1
    rw [this]) hs.2.2.1
  simp only [step]
  revert hf
  generalize s.pending.find? _ = a
  generalize s'.pending.find? _ = b
  intro hf
  cases hf with
  | none => exact ⟨hs, trivial, trivial, trivial⟩
  | @some p p' hp =>
    obtain ⟨pid, psnd, pext, preq⟩ := p
    obtain ⟨pid', psnd', pext', preq'⟩ := p'
    obtain ⟨-, -, -, hrq⟩ := hp
    cases hrq with
    | @mk name input output rejection value value' holds holds' onAnswer onAnswer' hval hholds hon =>
      dsimp only
      cases Ty.same t (answerTy output rejection) with
      | none => exact ⟨hs, trivial, trivial, trivial⟩
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
          refine finish_shift ho ⟨hrec, hmach, hpend, hnow, hfr, hn⟩
            (applyEvents_shift ho (hon (x, ()) (x', ()) ⟨hx, trivial⟩)
              (AccShift.ofState (s := { s with pending := s.pending.filter (·.id != to) })
                (s' := { s' with pending := s'.pending.filter (·.id != to) }) ⟨hrec, hmach, ?_, hnow, hfr, hn⟩))
            (o := .accepted) (o' := .accepted) trivial
          exact forall2_filter (fun p q h => by
            have : p.id = q.id := h.1
            rw [this]) hpend

/-- The step reads no bag's or table's order and no origin of time: from states the same up to that order and the
time shift `d`, on inputs the same up to them, it steps to results the same up to them, item by item. -/
theorem step_shift (ho : Ordered T v) {s s' : State v} (hs : StateShift d s s') {x x' : Input v}
    (hx : Input.Shift d x x') : ResultShift d (step T v s x) (step T v s' x') := by
  cases hx with
  | command i hc hi =>
    obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
    have hs1 : StateShift d { s with fresh := s.fresh + 1 } { s' with fresh := s'.fresh + 1 } :=
      ⟨hrec, hmach, hpend, hnow, by simp only [hfr], hn⟩
    have he := execCommand_shift ho (AccShift.ofState ⟨hrec, hmach, hpend, hnow, hfr, hn⟩) (List.get_mem _ _)
      (rel0_outside hc) hi
    simp only [step]
    revert he
    generalize execCommand T _ _ _ _ = y
    generalize execCommand T _ _ _ _ = y'
    intro he
    match y, y', he with
    | .error _, .error _, _ => exact ⟨hs1, trivial, trivial, trivial⟩
    | .ok (.invalid _), .ok (.invalid _), h => exact ⟨hs1, h, trivial, trivial⟩
    | .ok (.rejected _ _), .ok (.rejected _ _), ⟨_, hj⟩ => exact ⟨hs1, .mk hj, trivial, trivial⟩
    | .ok (.accepted _), .ok (.accepted _), hb => exact finish_shift ho hs1 (a := .ok _) (a' := .ok _) hb trivial
  | query i hc hi =>
    have he := execQuery_shift ho hs (List.get_mem _ _) (rel0_outside hc) hi
    simp only [step]
    revert he
    generalize execQuery s _ _ _ = y
    generalize execQuery s' _ _ _ = y'
    intro he
    match y, y', he with
    | .error _, .error _, h => exact ⟨hs, h, trivial, trivial⟩
    | .ok _, .ok _, h => exact ⟨hs, .mk h, trivial, trivial⟩
  | answer to hw =>
    cases hw with
    | mk hx => exact answer_shift ho hs to hx
  | @event i y y' hx =>
    obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
    simp only [step]
    exact finish_shift ho ⟨hrec, hmach, hpend, hnow, hfr, hn⟩
      (applyEvents_shift ho (evs := [_]) (evs' := [_])
        ⟨(ho.equi.self (PBij.shifted d)).subscribes _ (List.get_mem _ _) (y, ()) (y', ()) ⟨hx, trivial⟩, trivial⟩
        (AccShift.ofState ⟨hrec, hmach, hpend, hnow, hfr, hn⟩)) (o := .accepted) (o' := .accepted) trivial
  | @clock t t' ht =>
    simp only [step]
    have hlt := (PBij.point_ms_iff ht hs.2.2.2.1).2.2
    by_cases h : t < s.now
    · have h' : t' < s'.now := hlt.1 h
      simp only [h, h', ↓reduceIte]
      exact ⟨hs, rfl, trivial, trivial⟩
    · have h' : ¬ t' < s'.now := fun h' => h (hlt.2 h')
      simp only [h, h', ↓reduceIte]
      have hf := fire_shift ho (v.cascadeNat + 1) (s := { s with now := t }) (s' := { s' with now := t' })
        ⟨hs.1, hs.2.1, hs.2.2.1, ht, hs.2.2.2.2⟩
      revert hf
      generalize fire _ _ = p
      generalize fire _ _ = q
      intro hf
      cases hf with
      | none => exact ⟨hs, trivial, trivial, trivial⟩
      | some h =>
        exact finish_shift ho hs (start_shift h.2 (AccShift.ofState h.1)) trivial

/-- The step reads no bag's or table's order: from states the same up to that order, on inputs the same up to it, it
steps to results the same up to it, item by item. -/
theorem step_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') {x x' : Input v} (hx : Input.Same x x') :
    ResultSame (step T v s x) (step T v s' x') :=
  step_shift ho hs hx

end Step

end Tazuna.Ir
