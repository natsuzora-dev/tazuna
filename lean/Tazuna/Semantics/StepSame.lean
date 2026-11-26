import Tazuna.Semantics.StepRename

/-! The step does not read the order a bag or table is stored in. Two states are the same up to that order when their
records relate under the renaming that keeps every name (`Ty.rel0 PBij.refl`: bags and tables as multisets, everything
else equal) and every other part is equal item by item, in the same order: instances, pending requests, waiting own
effects, events and out lines (`StateSame`). Stepping such states on such inputs gives such results (`step_same`).
`StepRename` relates the collections only as multisets, since renaming fresh ids reorders keys; with every name kept,
the canonical order of instance keys (`machineStep`) is the same on both sides, so every effect starts, every own
command runs and every wire id is given in the same order. -/

namespace Tazuna.Ir

/-- The renaming that keeps every counter and every wire id. -/
def Ren.refl : Ren := ⟨PBij.refl, PBij.refl⟩

/-- Values the same up to the order their bags and tables are stored in. -/
abbrev Ty.Same (t : Ty) : t.den0 → t.den0 → Prop := Ty.rel0 PBij.refl t

theorem Ty.same_of_deq {t : Ty} (hc : t.comparable = true) {x y : t.den0} (h : t.deq0 x y = true) : Ty.Same t x y :=
  Ty.rel0_deq_right hc (Ty.rel0_refl t hc x) h

theorem Ty.deq_of_same {t : Ty} (hc : t.comparable = true) {x y : t.den0} (h : Ty.Same t x y) : t.deq0 x y = true := by
  rw [Ty.rel0_deq t hc h (Ty.rel0_refl t hc y)]; exact Ty.deq0_refl hc y

theorem Ty.same_trans {t : Ty} (hc : t.comparable = true) {x y z : t.den0} (h : Ty.Same t x y) (h' : Ty.Same t y z) :
    Ty.Same t x z :=
  Ty.rel0_deq_right hc h (Ty.deq_of_same hc h')

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

/-- Values the same up to order, put in the canonical order, are the same item by item: items of one Erlang term may
change places, and they are the same. -/
theorem Ty.sortBy_same (T : List TypeDecl) {t : Ty} (hc : t.comparable = true) (ho : t.ordered T = true)
    {xs ys : List t.den0} (h : Multi (Ty.Same t) xs ys) : Forall2 (Ty.Same t) (Ty.sortBy T t xs) (Ty.sortBy T t ys) := by
  obtain ⟨zs, hz, hp⟩ := h
  have herl : ∀ a b, Ty.Same t a b → Ty.erl T t a = Ty.erl T t b := fun a b hab =>
    (Ty.erl_iff T t ho a b).1 (Ty.deq_of_same hc hab)
  have h1 : Forall2 (Ty.Same t) (Ty.sortBy T t xs) (Ty.sortBy T t zs) :=
    forall2_mergeSort hz fun a b a' b' ha hb => by simp only [Ty.cmp, herl a a' ha, herl b b' hb]
  have hsort : ∀ l : List t.den0, (Ty.sortBy T t l).map (Ty.erl T t) = Erl.sort (l.map (Ty.erl T t)) := fun l => by
    unfold Ty.sortBy Erl.sort
    exact List.map_mergeSort (fun _ _ _ _ => rfl)
  have h2 : (Ty.sortBy T t zs).map (Ty.erl T t) = (Ty.sortBy T t ys).map (Ty.erl T t) := by
    rw [hsort, hsort]; exact (Erl.sort_eq_iff _ _).2 (hp.map _)
  have h3 := forall2_of_map_eq h2
  exact forall2_comp h1 (forall2_imp (fun a b e => Ty.same_of_deq hc ((Ty.erl_iff T t ho a b).2 e)) h3)
    |> forall2_imp fun _ _ ⟨_, h, h'⟩ => Ty.same_trans hc h h'

namespace Step

section Machine
variable {r e : Ty}

/-- Instances the same up to order, item by item. -/
abbrev Insts.Same {m : MachineV r e} : List (Instance m) → List (Instance m) → Prop := Forall2 (Instance.Rel PBij.refl)

def Machines.Same : {ms : List (MachineV r e)} → Machines ms → Machines ms → Prop
  | _, .nil, .nil => True
  | _, .cons l rest, .cons l' rest' => Insts.Same l l' ∧ Machines.Same rest rest'

theorem reactKey_same {m : MachineV r e} (hm : m.Equi) {insts insts' : List (Instance m)} (hl : Insts.Same insts insts')
    {records records' : r.den0} (hrec : Ty.Same r records records') (now : Int) {ev ev' : e.den0}
    (hev : Ty.Same e ev ev') {k k' : m.key.den0} (hk : Ty.Same m.key k k') :
    Reacted.Rel PBij.refl (reactKey m insts records now ev k) (reactKey m insts' records' now ev' k') := by
  unfold reactKey
  have hf := forall2_find? (p := (m.key.deq0 k ·.key)) (q := (m.key.deq0 k' ·.key))
    (fun a b hab => Ty.rel0_deq m.key hm.key hk hab.1) hl
  revert hf
  generalize insts.find? _ = a
  generalize insts'.find? _ = b
  intro hf
  cases hf with
  | none => exact enter_rel hm hrec now hk (hm.self _).initial
  | @some i i' hi =>
    dsimp only
    have hon := (hm.self PBij.refl).on (.inl (i.key, i.state, records, now, ()), ev, ())
      (.inl (i'.key, i'.state, records', now, ()), ev', ()) ⟨⟨hi.1, hi.2.1, hrec, rfl, trivial⟩, hev, trivial⟩
    revert hon
    generalize m.on.fn (.inl (i.key, i.state, records, now, ()), ev, ()) = x
    generalize m.on.fn (.inl (i'.key, i'.state, records', now, ()), ev', ()) = y
    intro hon
    match x, y, hon with
    | .inr (.inl (s, ())), .inr (.inl (s', ())), ⟨hs, _⟩ => exact enter_rel hm hrec now hi.1 hs
    | .inl (), .inl (), _ => exact ⟨hi, trivial⟩

theorem machineStep_same (T : List TypeDecl) {m : MachineV r e} (hm : m.Equi) (ho : m.key.ordered T = true)
    {records records' : r.den0} (hrec : Ty.Same r records records') (now : Int) {ev ev' : e.den0}
    (hev : Ty.Same e ev ev') {insts insts' : List (Instance m)} (hl : Insts.Same insts insts') :
    Insts.Same (machineStep T records now ev m insts).1 (machineStep T records' now ev' m insts').1 ∧
      Forall2 (Started.Rel PBij.refl) (machineStep T records now ev m insts).2
        (machineStep T records' now ev' m insts').2 := by
  have hb : Multi (Ty.Same m.key) (m.instances.fn (records, ())) (m.instances.fn (records', ())) :=
    (hm.self PBij.refl).instances _ _ ⟨hrec, trivial⟩
  have hd : Multi (Ty.Same m.key) (dedupBy m.key.deq0 (m.instances.fn (records, ())))
      (dedupBy m.key.deq0 (m.instances.fn (records', ()))) := by
    obtain ⟨zs, h, hz⟩ := hb
    exact ((Multi.of_forall2 (forall2_dedupBy (f := m.key.deq0) (f' := m.key.deq0)
      (fun _ _ _ _ => Ty.rel0_deq m.key hm.key) h)).comp
      (dedupBy_perm_multi (Ty.canon_iff m.key hm.key) hz)).imp fun _ _ ⟨_, h1, h2⟩ => Ty.rel0_deq_right hm.key h1 h2
  have hr := forall2_map2 (r' := Reacted.Rel PBij.refl) (fun _ _ hk => reactKey_same hm hl hrec now hev hk)
    (Ty.sortBy_same T hm.key ho hd)
  exact ⟨forall2_map2 (fun _ _ h => h.1) hr, forall2_flatMap2 (fun _ _ h => h.2) hr⟩

theorem reactMachines_same (T : List TypeDecl) {records records' : r.den0} (hrec : Ty.Same r records records')
    (now : Int) {ev ev' : e.den0} (hev : Ty.Same e ev ev') : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.Equi ∧ m.key.ordered T = true) → {l l' : Machines ms} → Machines.Same l l' →
    Machines.Same (reactMachines T records now ev l).1 (reactMachines T records' now ev' l').1 ∧
      Forall2 (Started.Rel PBij.refl) (reactMachines T records now ev l).2 (reactMachines T records' now ev' l').2
  | [], _, .nil, .nil, _ => ⟨trivial, trivial⟩
  | _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hx, hrest⟩ := h
    have hm := hms _ List.mem_cons_self
    have h1 := machineStep_same T hm.1 hm.2 hrec now hev hx
    have h2 := reactMachines_same T hrec now hev (fun m h => hms m (List.mem_cons_of_mem _ h)) hrest
    simp only [reactMachines]
    exact ⟨⟨h1.1, h2.1⟩, forall2_append h1.2 h2.2⟩

end Machine

variable {v : ServiceV}

/-- States the same up to the order their bags and tables are stored in. -/
def StateSame (s s' : State v) : Prop :=
  Ty.Same v.records s.records s'.records ∧ Machines.Same s.machines s'.machines ∧
    Forall2 (Pending.Rel Ren.refl) s.pending s'.pending ∧ s.now = s'.now ∧ s.fresh = s'.fresh ∧ s.nextId = s'.nextId

/-- Steps in progress the same up to that order. -/
def AccSame (a a' : Acc v) : Prop :=
  StateSame a.state a'.state ∧ Forall2 (Ty.Same v.event) a.events a'.events ∧
    Forall2 (OutLine.Rel Ren.refl) a.out a'.out ∧ Forall2 (OwnEffectV.Rel PBij.refl) a.own a'.own

/-- What runs from steps the same up to order end in: a fault on both sides, or steps the same up to order. -/
def ExSame : Except Fault (Acc v) → Except Fault (Acc v) → Prop
  | .error _, .error _ => True
  | .ok a, .ok a' => AccSame a a'
  | _, _ => False

theorem AccSame.ofState {s s' : State v} (h : StateSame s s') : AccSame ({ state := s } : Acc v) { state := s' } :=
  ⟨h, trivial, trivial, trivial⟩

theorem ExSame.bind {x x' : Except Fault (Acc v)} (h : ExSame x x') {f g : Acc v → Except Fault (Acc v)}
    (hfg : ∀ b b', AccSame b b' → ExSame (f b) (g b')) : ExSame (x >>= f) (x' >>= g) := by
  match x, x', h with
  | .error _, .error _, _ => trivial
  | .ok b, .ok b', h => exact hfg b b' h

/-- The machines and reactions with their functions respecting every renaming, and keys in a canonical order. -/
structure Ordered (T : List TypeDecl) (v : ServiceV) : Prop where
  equi : v.Equivariant
  keys : ∀ m ∈ v.machines, m.key.ordered T = true

variable {T : List TypeDecl}

theorem react_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') {ev ev' : v.event.den0}
    (hev : Ty.Same v.event ev ev') :
    StateSame (react T s ev).1 (react T s' ev').1 ∧
      Forall2 (Started.Rel PBij.refl) (react T s ev).2 (react T s' ev').2 := by
  obtain ⟨hrec, hmach, hpend, hnow, hf, hn⟩ := hs
  have hrec' : Ty.Same v.records (v.apply.fn (s.records, ev, ())) (v.apply.fn (s'.records, ev', ())) :=
    (ho.equi.self PBij.refl).apply _ _ ⟨hrec, hev, trivial⟩
  have hm := reactMachines_same T hrec' s.now hev
    (fun m hm => ⟨ho.equi.machines m hm, ho.keys m hm⟩) hmach
  unfold react
  dsimp only
  rw [← hnow]
  refine ⟨⟨hrec', hm.1, hpend, rfl, hf, hn⟩, forall2_append hm.2 ?_⟩
  have hx : ∀ x ∈ v.reactions, Forall2 (Started.Rel PBij.refl)
      ((x.effectsAt ev (v.apply.fn (s.records, ev, ())) s.now).map (.reaction x.name, ·))
      ((x.effectsAt ev' (v.apply.fn (s'.records, ev', ())) s.now).map (.reaction x.name, ·)) := fun x hx =>
    forall2_map2 (fun _ _ h => ⟨.reaction x.name, h⟩)
      (EffectFun.apply_rel x.react ((ho.equi.self PBij.refl).reactions x hx) ⟨⟨hrec', rfl, trivial⟩, hev, trivial⟩)
  clear hm hpend
  revert hx
  induction v.reactions with
  | nil => intro; trivial
  | cons x xs ih =>
    intro hx
    simp only [List.flatMap_cons]
    exact forall2_append (hx x List.mem_cons_self) (ih fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem start_same : {effs effs' : List (Sender × EffectV v.event)} → Forall2 (Started.Rel PBij.refl) effs effs' →
    {a a' : Acc v} → AccSame a a' → ExSame (start a effs) (start a' effs')
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
        have hline : OutLine.Rel Ren.refl ⟨a.state.nextId, x, r.name, ⟨r.input, r.value⟩⟩
            ⟨a'.state.nextId, x, r'.name, ⟨r'.input, r'.value⟩⟩ := by
          cases hrr with
          | mk _ _ _ _ hv _ _ => exact ⟨hn, rfl, rfl, .mk hv⟩
        exact start_same h ⟨⟨hrec, hmach, forall2_append hpend ⟨⟨hn, hs, rfl, hrr⟩, trivial⟩, hnow, hf,
          by simp only [hn]⟩, hev, forall2_append hout ⟨hline, trivial⟩, hown⟩
    | command name c i j hc hval hf =>
      obtain ⟨hst, hev, hout, hown⟩ := ha
      exact start_same h ⟨hst, hev, hout, forall2_append hown ⟨.command _ _ _ _ hc hval hf, trivial⟩⟩
    | query name c i o hc hval hf =>
      obtain ⟨hst, hev, hout, hown⟩ := ha
      exact start_same h ⟨hst, hev, hout, forall2_append hown ⟨.query _ _ _ _ hc hval hf, trivial⟩⟩
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

theorem applyEvents_same (ho : Ordered T v) : {evs evs' : List v.event.den0} → Forall2 (Ty.Same v.event) evs evs' →
    {a a' : Acc v} → AccSame a a' → ExSame (applyEvents T a evs) (applyEvents T a' evs')
  | [], [], _, _, _, ha => ha
  | ev :: evs, ev' :: evs', ⟨hev, h⟩, a, a', ha => by
    unfold applyEvents
    rw [List.foldlM_cons, List.foldlM_cons]
    have hr := react_same ho ha.1 hev
    obtain ⟨_, hevs, hout, hown⟩ := ha
    refine (start_same hr.2 (a := { a with state := (react T a.state ev).1, events := a.events ++ [ev] })
      (a' := { a' with state := (react T a'.state ev').1, events := a'.events ++ [ev'] })
      ⟨hr.1, forall2_append hevs ⟨hev, trivial⟩, hout, hown⟩).bind fun b b' hb => ?_
    exact applyEvents_same ho h hb
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

/-- What a command's runs from steps the same up to order end in. -/
def RanSame {j : Ty} : Except Fault (Ran v j) → Except Fault (Ran v j) → Prop
  | .error _, .error _ => True
  | .ok (.invalid rs), .ok (.invalid rs') => rs = rs'
  | .ok (.rejected a x), .ok (.rejected a' x') => AccSame a a' ∧ Ty.Same j x x'
  | .ok (.accepted a), .ok (.accepted a') => AccSame a a'
  | _, _ => False

theorem execCommand_same (ho : Ordered T v) {a a' : Acc v} (ha : AccSame a a')
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c c' : v.caller.den0} (hc : Ty.Same v.caller c c')
    {i i' : x.input.den0} (hi : Ty.Same x.input i i') :
    RanSame (execCommand T a x c i) (execCommand T a' x c' i') := by
  obtain ⟨hcl, hacc, hdec, hens⟩ := (ho.equi.self PBij.refl).commands x hx
  unfold execCommand
  rw [admit_rel ho.equi hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => rfl
  | nil =>
    dsimp only
    have hcx : Ty.Same (Ty.ctx v.records x.input v.caller) (ctx a.state a.state.records c i)
        (ctx a'.state a'.state.records c' i') := ⟨ha.1.1, hi, hc, ha.1.2.2.2.1, ha.1.2.2.2.2.1, trivial⟩
    have hd := hdec (ctx a.state a.state.records c i, ()) (ctx a'.state a'.state.records c' i', ()) ⟨hcx, trivial⟩
    revert hd
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = d
    generalize x.decide.fn (ctx a'.state a'.state.records c' i', ()) = d'
    intro hd
    obtain ⟨⟨hrec, hmach, hpend, hnow, hf, hn⟩, hevs0, hout, hown⟩ := ha
    have ha1 : AccSame { a with state := { a.state with fresh := a.state.fresh + 1 } }
        { a' with state := { a'.state with fresh := a'.state.fresh + 1 } } :=
      ⟨⟨hrec, hmach, hpend, hnow, by simp only [hf], hn⟩, hevs0, hout, hown⟩
    match d, d', hd with
    | .inl (evs, ()), .inl (evs', ()), ⟨hevs, _⟩ =>
      dsimp only
      have he := applyEvents_same ho hevs ha1
      revert he
      generalize applyEvents T _ evs = y
      generalize applyEvents T _ evs' = y'
      intro he
      match y, y', he with
      | .error _, .error _, _ => trivial
      | .ok b, .ok b', hb =>
        show RanSame (match broken _ with | _ :: _ => _ | [] => _) (match broken _ with | _ :: _ => _ | [] => _)
        rw [broken_rel (hens (ctx a.state a.state.records c i, b.state.records, ())
          (ctx a'.state a'.state.records c' i', b'.state.records, ()) ⟨hcx, hb.1.1, trivial⟩)]
        cases broken (x.ensures.fn (ctx a'.state a'.state.records c' i', b'.state.records, ())) with
        | cons n ns => trivial
        | nil => exact hb
    | .inr (.inl (j, ())), .inr (.inl (j', ())), ⟨hj, _⟩ => exact ⟨ha1, hj⟩

theorem runCommand_same (ho : Ordered T v) {a a' : Acc v} (ha : AccSame a a')
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c c' : v.caller.den0} (hc : Ty.Same v.caller c c')
    {i i' : x.input.den0} (hi : Ty.Same x.input i i')
    {f f' : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))} (hf : Fun.Rel PBij.refl f f') :
    ExSame (runCommand T a x c i f) (runCommand T a' x c' i' f') := by
  have he := execCommand_same ho ha hx hc hi
  unfold runCommand
  revert he
  generalize execCommand T a x c i = y
  generalize execCommand T a' x c' i' = y'
  intro he
  match y, y', he with
  | .error _, .error _, _ => trivial
  | .ok (.invalid _), .ok (.invalid _), _ => trivial
  | .ok (.accepted b), .ok (.accepted b'), hb =>
    exact applyEvents_same ho (hf (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) hb
  | .ok (.rejected b j), .ok (.rejected b' j'), ⟨hb, hj⟩ =>
    exact applyEvents_same ho (hf (.inr (.inl (j, ())), ()) (.inr (.inl (j', ())), ()) ⟨⟨hj, trivial⟩, trivial⟩) hb

theorem execQuery_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c c' : v.caller.den0} (hc : Ty.Same v.caller c c') {i i' : x.input.den0}
    (hi : Ty.Same x.input i i') :
    match execQuery s x c i, execQuery s' x c' i' with
    | .error rs, .error rs' => rs = rs'
    | .ok o, .ok o' => Ty.Same x.output o o'
    | _, _ => False := by
  obtain ⟨hcl, hacc, hres⟩ := (ho.equi.self PBij.refl).queries x hx
  unfold execQuery
  rw [admit_rel ho.equi hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => rfl
  | nil =>
    exact hres (queryCtx s s.records c i, ()) (queryCtx s' s'.records c' i', ())
      ⟨⟨hs.1, hi, hc, hs.2.2.2.1, trivial⟩, trivial⟩

theorem runQuery_same (ho : Ordered T v) {a a' : Acc v} (ha : AccSame a a') {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c c' : v.caller.den0} (hc : Ty.Same v.caller c c') {i i' : x.input.den0}
    (hi : Ty.Same x.input i i') {f f' : Fun (Ty.fn [x.output] (.list v.event))} (hf : Fun.Rel PBij.refl f f') :
    ExSame (runQuery T a x c i f) (runQuery T a' x c' i' f') := by
  have he := execQuery_same ho ha.1 hx hc hi
  unfold runQuery
  revert he
  generalize execQuery a.state x c i = y
  generalize execQuery a'.state x c' i' = y'
  intro he
  obtain ⟨⟨hrec, hmach, hpend, hnow, hfr, hn⟩, hevs0, hout, hown⟩ := ha
  match y, y', he with
  | .error _, .error _, _ => trivial
  | .ok o, .ok o', ho' =>
    exact applyEvents_same ho (hf (o, ()) (o', ()) ⟨ho', trivial⟩)
      ⟨⟨hrec, hmach, hpend, hnow, by simp only [hfr], hn⟩, hevs0, hout, hown⟩

theorem runOwn_same (ho : Ordered T v) {a a' : Acc v} (ha : AccSame a a') {eff eff' : OwnEffectV v.event}
    (he : OwnEffectV.Rel PBij.refl eff eff') : ExSame (runOwn T a eff) (runOwn T a' eff') := by
  cases he with
  | command name c i j hc hval hf =>
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
        exact runCommand_same ho ha hmem hc hval hf
  | query name c i o hc hval hf =>
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
        exact runQuery_same ho ha hmem hc hval hf

theorem settle_same (ho : Ordered T v) : (fuel : Nat) → {a a' : Acc v} → AccSame a a' →
    ExSame (settle T fuel a) (settle T fuel a')
  | fuel, a, a', ha => by
    have hown := ha.2.2.2
    unfold settle
    match h1 : a.own, h2 : a'.own, fuel, hown with
    | [], [], _, _ => exact ha
    | _ :: _, _ :: _, 0, _ => trivial
    | eff :: rest, eff' :: rest', f + 1, ⟨he, hr⟩ =>
      dsimp only
      obtain ⟨hst, hevs, hout, -⟩ := ha
      exact (runOwn_same ho (a := { a with own := rest }) (a' := { a' with own := rest' }) ⟨hst, hevs, hout, hr⟩
        he).bind fun b b' hb => settle_same ho f hb
    | [], _ :: _, _, h | _ :: _, [], _, h => exact h.elim

theorem machineInvariants_same {records records' : v.records.den0} (hrec : Ty.Same v.records records records')
    (now : Int) : {ms : List (MachineV v.records v.event)} → (∀ m ∈ ms, m.Equi) → {l l' : Machines ms} →
    Machines.Same l l' →
    (l.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        broken (m.invariants.fn (.inl (i.key, i.state, records, now, ()), ()))) =
      (l'.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        broken (m.invariants.fn (.inl (i.key, i.state, records', now, ()), ())))
  | [], _, .nil, .nil, _ => rfl
  | m :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    rw [machineInvariants_same hrec now (fun m' h => hms m' (List.mem_cons_of_mem _ h)) hr]
    refine congrArg (· ++ _) (forall2_flatMap (fun i i' h => ?_) hi)
    exact broken_rel (((hms m List.mem_cons_self).self PBij.refl).invariants _ _
      ⟨⟨h.1, h.2.1, hrec, rfl, trivial⟩, trivial⟩)

theorem invariants_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') :
    invariants s = invariants s' := by
  obtain ⟨hrec, hmach, -, hnow, -, -⟩ := hs
  unfold invariants
  rw [← hnow]
  rw [machineInvariants_same hrec s.now ho.equi.machines hmach]
  exact congrArg (· ++ _) (broken_rel ((ho.equi.self PBij.refl).invariants _ _ ⟨hrec, trivial⟩))

/-- Outcomes the same up to order: a fault on both sides, or the same outcome with values the same up to order. -/
def Outcome.Same : Outcome → Outcome → Prop
  | .accepted, .accepted => True
  | .answered w, .answered w' => WireVal.Rel PBij.refl w w'
  | .rejected w, .rejected w' => WireVal.Rel PBij.refl w w'
  | .invalid rs, .invalid rs' => rs = rs'
  | .fault _, .fault _ => True
  | _, _ => False

/-- Results the same up to order. -/
def ResultSame (r r' : Result v) : Prop :=
  StateSame r.state r'.state ∧ Outcome.Same r.outcome r'.outcome ∧ Forall2 (Ty.Same v.event) r.events r'.events ∧
    Forall2 (OutLine.Rel Ren.refl) r.out r'.out

theorem finish_same (ho : Ordered T v) {s0 s0' : State v} (hs0 : StateSame s0 s0') {a a' : Except Fault (Acc v)}
    (ha : ExSame a a') {o o' : Outcome} (hoo : Outcome.Same o o') :
    ResultSame (finish T s0 a o) (finish T s0' a' o') := by
  have h := ha.bind fun b b' hb => settle_same ho v.bounds.cascadeNat hb
  unfold finish
  revert h
  generalize a >>= settle T v.bounds.cascadeNat = y
  generalize a' >>= settle T v.bounds.cascadeNat = y'
  intro h
  match y, y', h with
  | .error _, .error _, _ => exact ⟨hs0, trivial, trivial, trivial⟩
  | .ok b, .ok b', hb =>
    dsimp only
    rw [invariants_same ho hb.1]
    cases invariants b'.state with
    | cons n ns => exact ⟨hs0, trivial, trivial, trivial⟩
    | nil => exact ⟨hb.1, hoo, hb.2.1, hb.2.2.1⟩

section Fire
variable {r e : Ty}

theorem fireFirst_same {m : MachineV r e} (hm : m.Equi) {records records' : r.den0} (hrec : Ty.Same r records records')
    (now d : Int) : {l l' : List (Instance m)} → Insts.Same l l' →
    Insts.Same (fireFirst m records now d l).1 (fireFirst m records' now d l').1 ∧
      Forall2 (Started.Rel PBij.refl) (fireFirst m records now d l).2.1 (fireFirst m records' now d l').2.1 ∧
      (fireFirst m records now d l).2.2 = (fireFirst m records' now d l').2.2
  | [], [], _ => ⟨trivial, trivial, rfl⟩
  | i :: is, i' :: is', ⟨hi, h⟩ => by
    have ih := fireFirst_same hm hrec now d h
    have hhit : hitsAt d i = hitsAt d i' := by
      have ht := hi.2.2
      unfold hitsAt
      revert ht
      generalize i.timer = a
      generalize i'.timer = b
      intro ht
      cases ht with
      | none => rfl
      | @some a b hab =>
        obtain ⟨a1, a2⟩ := a
        obtain ⟨b1, b2⟩ := b
        obtain ⟨rfl, -⟩ := hab
        rfl
    have hfired : Reacted.Rel PBij.refl (fired m records now i) (fired m records' now i') := by
      have ht := hi.2.2
      unfold fired
      revert ht
      generalize i.timer = a
      generalize i'.timer = b
      intro ht
      cases ht with
      | none => exact ⟨hi, trivial⟩
      | some hab => exact enter_rel hm hrec now hi.1 hab.2
    simp only [fireFirst, hhit]
    split
    · exact ⟨⟨hfired.1, h⟩, hfired.2, rfl⟩
    · exact ⟨⟨hi, ih.1⟩, ih.2.1, ih.2.2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem fireMachines_same {records records' : r.den0} (hrec : Ty.Same r records records') (now d : Int) :
    (done : Bool) → {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi) → {l l' : Machines ms} → Machines.Same l l' →
    Machines.Same (fireMachines records now d done l).1 (fireMachines records' now d done l').1 ∧
      Forall2 (Started.Rel PBij.refl) (fireMachines records now d done l).2.1
        (fireMachines records' now d done l').2.1 ∧
      (fireMachines records now d done l).2.2 = (fireMachines records' now d done l').2.2
  | _, [], _, .nil, .nil, _ => ⟨trivial, trivial, rfl⟩
  | true, _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    have ih := fireMachines_same hrec now d true (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    exact ⟨⟨hi, ih.1⟩, ih.2.1, rfl⟩
  | false, m :: _, hms, .cons l _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    have hy := fireFirst_same (hms _ List.mem_cons_self) hrec now d hi
    simp only [fireMachines]
    rw [← hy.2.2]
    have ih := fireMachines_same hrec now d (fireFirst m records now d l).2.2
      (fun m h => hms m (List.mem_cons_of_mem _ h)) hr
    exact ⟨⟨hy.1, ih.1⟩, forall2_append hy.2.1 ih.2.1, ih.2.2⟩

theorem dues_same {now : Int} : {ms : List (MachineV r e)} → {l l' : Machines ms} → Machines.Same l l' →
    dues l.toSigma now = dues l'.toSigma now
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, h => by
    obtain ⟨hi, hr⟩ := h
    unfold dues
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    have ih := dues_same (now := now) hr
    unfold dues at ih
    rw [ih]
    refine congrArg (· ++ _) ?_
    refine forall2_eq (forall2_filterMap (r' := (· = ·)) (fun i i' h => ?_) hi)
    have ht := h.2.2
    revert ht
    generalize i.timer = a
    generalize i'.timer = b
    intro ht
    cases ht with
    | none => exact .none
    | @some a b hab =>
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      obtain ⟨rfl, -⟩ := hab
      simp only [Option.bind_some]
      split
      · exact .some rfl
      · exact .none

end Fire

theorem fire_same (ho : Ordered T v) : (fuel : Nat) → {s s' : State v} → StateSame s s' →
    Option.Rel (fun x y => StateSame x.1 y.1 ∧ Forall2 (Started.Rel PBij.refl) x.2 y.2) (fire s fuel) (fire s' fuel)
  | 0, _, _, _ => .none
  | fuel + 1, s, s', hs => by
    unfold fire
    rw [dues_same hs.2.1, ← hs.2.2.2.1]
    cases (dues s'.machines.toSigma s.now).min? with
    | none => exact .some ⟨hs, trivial⟩
    | some d =>
      dsimp only
      have hx := fireMachines_same hs.1 s.now d false ho.equi.machines hs.2.1
      obtain ⟨hrec, -, hpend, hnow, hf, hn⟩ := hs
      have ih := fire_same ho fuel (s := { s with machines := (fireMachines s.records s.now d false s.machines).1 })
        (s' := { s' with machines := (fireMachines s'.records s.now d false s'.machines).1 })
        ⟨hrec, hx.1, hpend, hnow, hf, hn⟩
      rw [hnow] at ih hx ⊢
      revert ih
      generalize fire _ fuel = p
      generalize fire _ fuel = q
      intro ih
      cases ih with
      | none => exact .none
      | some h => exact .some ⟨h.1, forall2_append hx.2.1 h.2⟩

/-- Inputs the same up to the order of their values' bags and tables. -/
inductive Input.Same : Input v → Input v → Prop
  | command (i : Fin v.commands.length) {c c' : v.caller.den0} {x x' : (v.commands.get i).input.den0} :
      Ty.Same v.caller c c' → Ty.Same _ x x' → Input.Same (.command i c x) (.command i c' x')
  | query (i : Fin v.queries.length) {c c' : v.caller.den0} {x x' : (v.queries.get i).input.den0} :
      Ty.Same v.caller c c' → Ty.Same _ x x' → Input.Same (.query i c x) (.query i c' x')
  | answer (to : Nat) {w w' : WireVal} : WireVal.Rel PBij.refl w w' → Input.Same (.answer to w) (.answer to w')
  | event (i : Fin v.subscribes.length) {x x' : (v.subscribes.get i).event.den0} :
      Ty.Same _ x x' → Input.Same (.event i x) (.event i x')
  | clock (t : Int) : Input.Same (.clock t) (.clock t)

theorem answer_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') (to : Nat) {t : Ty} {x x' : t.den0}
    (hx : Ty.Same t x x') : ResultSame (step T v s (.answer to ⟨t, x⟩)) (step T v s' (.answer to ⟨t, x'⟩)) := by
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
          refine finish_same ho ⟨hrec, hmach, hpend, hnow, hfr, hn⟩
            (applyEvents_same ho (hon (x, ()) (x', ()) ⟨hx, trivial⟩)
              (AccSame.ofState (s := { s with pending := s.pending.filter (·.id != to) })
                (s' := { s' with pending := s'.pending.filter (·.id != to) }) ⟨hrec, hmach, ?_, hnow, hfr, hn⟩))
            (o := .accepted) (o' := .accepted) trivial
          exact forall2_filter (fun p q h => by
            have : p.id = q.id := h.1
            rw [this]) hpend

/-- The step reads no bag's or table's order: from states the same up to that order, on inputs the same up to it, it
steps to results the same up to it, item by item. -/
theorem step_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') {x x' : Input v} (hx : Input.Same x x') :
    ResultSame (step T v s x) (step T v s' x') := by
  cases hx with
  | command i hc hi =>
    obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
    have hs1 : StateSame { s with fresh := s.fresh + 1 } { s' with fresh := s'.fresh + 1 } :=
      ⟨hrec, hmach, hpend, hnow, by simp only [hfr], hn⟩
    have he := execCommand_same ho (AccSame.ofState ⟨hrec, hmach, hpend, hnow, hfr, hn⟩) (List.get_mem _ _) hc hi
    simp only [step]
    revert he
    generalize execCommand T _ _ _ _ = y
    generalize execCommand T _ _ _ _ = y'
    intro he
    match y, y', he with
    | .error _, .error _, _ => exact ⟨hs1, trivial, trivial, trivial⟩
    | .ok (.invalid _), .ok (.invalid _), h => exact ⟨hs1, h, trivial, trivial⟩
    | .ok (.rejected _ _), .ok (.rejected _ _), ⟨_, hj⟩ => exact ⟨hs1, .mk hj, trivial, trivial⟩
    | .ok (.accepted _), .ok (.accepted _), hb => exact finish_same ho hs1 (a := .ok _) (a' := .ok _) hb trivial
  | query i hc hi =>
    have he := execQuery_same ho hs (List.get_mem _ _) hc hi
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
    | mk hx => exact answer_same ho hs to hx
  | @event i y y' hx =>
    obtain ⟨hrec, hmach, hpend, hnow, hfr, hn⟩ := hs
    simp only [step]
    exact finish_same ho ⟨hrec, hmach, hpend, hnow, hfr, hn⟩
      (applyEvents_same ho (evs := [_]) (evs' := [_])
        ⟨(ho.equi.self PBij.refl).subscribes _ (List.get_mem _ _) (y, ()) (y', ()) ⟨hx, trivial⟩, trivial⟩
        (AccSame.ofState ⟨hrec, hmach, hpend, hnow, hfr, hn⟩)) (o := .accepted) (o' := .accepted) trivial
  | clock t =>
    simp only [step]
    rw [hs.2.2.2.1]
    split
    · exact ⟨hs, rfl, trivial, trivial⟩
    · have hf := fire_same ho (v.bounds.cascadeNat + 1) (s := { s with now := t }) (s' := { s' with now := t })
        ⟨hs.1, hs.2.1, hs.2.2.1, rfl, hs.2.2.2.2⟩
      revert hf
      generalize fire _ _ = p
      generalize fire _ _ = q
      intro hf
      cases hf with
      | none => exact ⟨hs, trivial, trivial, trivial⟩
      | some h =>
        exact finish_same ho hs (start_same h.2 (AccSame.ofState h.1)) trivial

end Step

end Tazuna.Ir
