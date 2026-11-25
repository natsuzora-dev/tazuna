import Tazuna.Smt.Layout
import Tazuna.Smt.EventPending
import Tazuna.Smt.Bounds

/-! The layout of a service's scripts, derived from its program and bounds (`Layout.ofService`), with nothing to state
by hand. Its kinds of effect are the request shapes the pending table already uses (`requestShapes`, so the two
cannot drift) and, for own commands and queries, each handle the program makes with each `on_answer` site of its
type; its datatypes are those of every expression type of the program and of the step's own types; a table type gets
the slots its creates bound (`boundSlots`), a bag `items`, a list its longest literal (`listSlots`). The collection
follows whole-program type collection as in monomorphization; the order puts each datatype after the ones its fields
use, as SMT-LIB's declarations need. `ofService_has` proves every one of those types has its datatypes, so the step
environment is found (`stepEnv_ofService`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {G : List Ty}

/-- The type of every node of every definition. -/
def _root_.Tazuna.Ir.Defs.tys : {G : List Ty} → Defs G → List Ty
  | [], .nil => []
  | _ :: _, .snoc defs _ body => defs.tys ++ Tazuna.Smt.Expr.tys body

/-- The type and length of every list literal of every definition. -/
def _root_.Tazuna.Ir.Defs.lits : {G : List Ty} → Defs G → List (Ty × Nat)
  | [], .nil => []
  | _ :: _, .snoc defs _ body => defs.lits ++ Tazuna.Smt.Expr.lits body

end


/-- The kind of effect of a request shape: its variant's key, the sites by their ids. -/
def _root_.Tazuna.Ir.RequestShape.key {e : Ty} (sh : RequestShape e) : EffectKey :=
  ⟨e, sh.name, sh.input, sh.output, sh.rejection, sh.ensures.map (fun s => ⟨s.2.site, s.1⟩),
    ⟨sh.onAnswer.site, sh.answerΓ⟩⟩

/-- The own kinds of effect that a command or query handle makes, of each event type `es` lists for a query, one per
`on_answer` site of its type. A handle of a command the service does not list still gets its kinds: its effects run
as `Fault.invalidEffect`, and the encoder needs their variant to say so. -/
def ownKeys (es : List Ty) (P : List AnySite) (h : HandleSite) : List OwnKey :=
  match h.kind, h.name, h.types with
  | "command", some n, [_, e, c, i, j] =>
    (sitesOf P (Ty.fn [Ty.result Ty.nil j] (.list e))).map fun s => .command e n c i j ⟨s.2.site, s.1⟩
  | "query", some n, [_, c, i, o] => es.flatMap fun e =>
    (sitesOf P (Ty.fn [o] (.list e))).map fun s => .query e n c i o ⟨s.2.site, s.1⟩
  | _, _, _ => []

/-- The types a step of the service codes beyond its program's expressions: the state's, the input's, what
`StepEnv` looks up, and the tuple of each sender's key, which a start writes whether or not a request has a shape. -/
def stepTys (v : ServiceV) (P : List AnySite) : List Ty :=
  [v.records, v.event, v.caller, Ty.option (.dsl .effect [v.event]), pendingTable (shapes v P), .tuple []] ++
    v.machines.map (·.table) ++ v.machines.map (fun m => .tuple [m.key])

/-- What the layout builder reads of a program: its sites, its handles, the type of every node and every list
literal's type and length. -/
structure ProgramParts where
  sites : List AnySite
  handles : List HandleSite
  tys : List Ty
  lits : List (Ty × Nat)

def _root_.Tazuna.Ir.Defs.parts {G : List Ty} (defs : Defs G) : ProgramParts :=
  ⟨defs.sites, defs.handles, defs.tys, defs.lits⟩

/-- The event types an effect of the program can have a kind of: the service's first, then each whose list a site of
one argument returns, as an `on_answer` does. Any code of the program may run in a step, another service's
included. -/
def eventTys (p : ProgramParts) (v : ServiceV) : List Ty :=
  dedupBy (fun a b => (Ty.same a b).isSome)
    (v.event :: p.sites.filterMap fun ⟨_, t, _⟩ => match t with | .fn [_] (.list e) => some e | _ => none)

/-- The kinds of effect of the service's scripts, from the program it came from, before any datatype: those whose
fields are data with sorts, so every datatype of the layout has one. -/
def Layout.kindsOf (p : ProgramParts) (v : ServiceV) : Layout :=
  { effects := dedupBy EffectKey.same (((eventTys p v).flatMap fun e =>
      (requestShapesAt v.declared e p.sites).map (·.key)).filter fun k => Ty.sorteds k.fields && (Ty.tuple k.fields).isData),
    owns := dedupBy OwnKey.same ((p.handles.flatMap (ownKeys (eventTys p v) p.sites)).filter fun k => Ty.sorteds k.fields && (Ty.tuple k.fields).isData) }

/-- The types the step's encoders build beyond the state's: contexts, functions' results, rules, event and effect
lists, answers and own commands' answers. They are listed after the program's types, which already hold them where a
function of the program has them, so the layout keeps its order. -/
def useTys (v : ServiceV) (P : List AnySite) (K : Layout) : List Ty :=
  [Ty.rules, .list v.event] ++
    v.reactions.flatMap (fun _ => [Ty.reactionCtx v.records, .list (.dsl .effect [v.event])]) ++
    v.machines.flatMap (fun m => [Ty.machineCtx m.key m.state v.records, Ty.next m.state, Ty.option (Ty.timer m.state),
      .bag m.key]) ++
    v.commands.flatMap (fun x => [Ty.ctx v.records x.input v.caller, Ty.result (.list v.event) x.rejection]) ++
    v.queries.flatMap (fun q => [Ty.ctx v.records q.input v.caller, q.output]) ++
    v.subscribes.map (·.event) ++
    (shapes v P).map (fun sh => answerTy sh.output sh.rejection) ++
    K.owns.flatMap fun
      | .command _ _ _ _ j a => [Ty.nil, Ty.result Ty.nil j, .tuple a.Γ]
      | .query _ _ _ _ _ a => [.tuple a.Γ]

/-- The slots of a type: its bound's, and at least `items` for a machine's instance table, which holds an instance
per key of its instances bag; a records table of the same type shares its datatype. -/
def stepSlots (v : ServiceV) (t : Ty) : Nat :=
  if v.machines.any (fun m => (Ty.same m.table t).isSome) then max (boundSlots v.bounds t) v.bounds.itemsNat
  else boundSlots v.bounds t

/-- The layout of the service's scripts, from the program it came from: the datatypes of the types with sorts. -/
def Layout.ofParts (p : ProgramParts) (v : ServiceV) : Layout :=
  Layout.addTys (listSlots (stepSlots v) p.lits) (Layout.kindsOf p v)
    ((stepTys v p.sites ++ p.tys ++ useTys v p.sites (Layout.kindsOf p v)).filter Ty.sortable)

/-- The layout of the service's scripts, from the program `defs` it came from. -/
abbrev Layout.ofService {G : List Ty} (defs : Defs G) (v : ServiceV) : Layout := Layout.ofParts defs.parts v

theorem hasWiths_mem {L : Layout} {D : Dsl → List Ty → Prop} : {ts : List Ty} → Layout.HasWiths L D ts →
    ∀ t ∈ ts, Layout.HasWith L D t
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, h⟩, t, .tail _ ht => hasWiths_mem h t ht

/-- Every step type and every expression type of the program that has a sort has its datatypes in the service's
layout. -/
theorem ofService_has {G : List Ty} (defs : Defs G) (v : ServiceV) :
    ∀ t ∈ (stepTys v defs.sites ++ defs.tys ++ useTys v defs.sites (Layout.kindsOf defs.parts v)).filter Ty.sortable,
      (Layout.ofService defs v).Has t :=
  hasWiths_mem (Layout.addTys_has _ _ _)

theorem find_of_has_option {L : Layout} {e : Ty} (h : L.Has (Ty.option (.dsl .effect [e]))) :
    (L.find? (.dsl .effect [e])).isSome = true ∧ (L.find? (Ty.option (.dsl .effect [e]))).isSome = true :=
  ⟨h.1.1.1.2, h.2⟩

theorem collD_of_has_table {L : Layout} {k w : Ty} (h : L.Has (.table k w)) : ∃ x, collD L (.table k w) [k, w] = .ok x := by
  obtain ⟨-, -, ht, hc⟩ := h
  obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 ht
  exact ⟨(d, n, dt), by simp [collD, hd, hdt]⟩

/-- Every datatype of the layout holds the slots `S` gives its type, and its kinds of effect are `K`'s. -/
def Slotted (S : Ty → Nat) (K L : Layout) : Prop := (∀ p ∈ L.types, p.2 = S p.1) ∧ L.effects = K.effects ∧ L.owns = K.owns

/-- `S` gives no slots to a type that is no collection, as the builder pushes those. -/
def NoSlots (S : Ty → Nat) : Prop := ∀ t, (∀ u, t ≠ .bag u) → (∀ u, t ≠ .list u) → (∀ k w, t ≠ .table k w) → S t = 0

theorem slotted_push {S : Ty → Nat} {K L : Layout} (h : Slotted S K L) (t : Ty) (n : Nat) (hn : n = S t) :
    Slotted S K (L.push t n) := by
  unfold Layout.push; split
  · exact h
  · refine ⟨fun p hp => ?_, h.2⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact h.1 p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact hn

section
variable {S : Ty → Nat} {K : Layout} {dsl : Layout → Dsl → List Ty → Layout}

mutual
theorem slotted_addTyWith (hS : NoSlots S) (hd : ∀ L k a, Slotted S K L → Slotted S K (dsl L k a)) :
    (L : Layout) → Slotted S K L → (t : Ty) → Slotted S K (Layout.addTyWith S dsl L t)
  | L, h, .tuple ts => slotted_push (slotted_addTysWith hS hd L h ts) _ _ (hS _ (by simp) (by simp) (by simp)).symm
  | L, h, .adt 0 a vs => by
    simp only [Layout.addTyWith]; split
    · exact h
    · exact slotted_push (slotted_addTyssWith hS hd L h vs) _ _ (hS _ (by simp) (by simp) (by simp)).symm
  | L, h, .adt (i + 1) a vs =>
    slotted_push (slotted_addTyssWith hS hd L h vs) _ _ (hS _ (by simp) (by simp) (by simp)).symm
  | L, h, .id => slotted_push h _ _ (hS _ (by simp) (by simp) (by simp)).symm
  | L, h, .list t =>
    slotted_push (slotted_push (slotted_addTyWith hS hd L h t) _ _ (hS _ (by simp) (by simp) (by simp)).symm) _ _ rfl
  | L, h, .bag t =>
    slotted_push (slotted_push (slotted_addTyWith hS hd L h t) _ _ (hS _ (by simp) (by simp) (by simp)).symm) _ _ rfl
  | L, h, .table k v =>
    slotted_push (slotted_push (slotted_addTyWith hS hd _ (slotted_addTyWith hS hd L h k) v) _ _
      (hS _ (by simp) (by simp) (by simp)).symm) _ _ rfl
  | L, h, .fn ps r => slotted_addTyWith hS hd _ (slotted_addTysWith hS hd L h ps) r
  | L, h, .dsl k a => hd L k a h
  | _, h, .int | _, h, .str | _, h, .date | _, h, .param _ => h
theorem slotted_addTysWith (hS : NoSlots S) (hd : ∀ L k a, Slotted S K L → Slotted S K (dsl L k a)) :
    (L : Layout) → Slotted S K L → (ts : List Ty) → Slotted S K (Layout.addTysWith S dsl L ts)
  | _, h, [] => h
  | L, h, t :: ts => slotted_addTysWith hS hd _ (slotted_addTyWith hS hd L h t) ts
theorem slotted_addTyssWith (hS : NoSlots S) (hd : ∀ L k a, Slotted S K L → Slotted S K (dsl L k a)) :
    (L : Layout) → Slotted S K L → (vs : List (List Ty)) → Slotted S K (Layout.addTyssWith S dsl L vs)
  | _, h, [] => h
  | L, h, ts :: vs => slotted_addTyssWith hS hd _ (slotted_addTysWith hS hd L h ts) vs
end

end

theorem slotted_fold {S : Ty → Nat} {K : Layout} (hS : NoSlots S) : (fss : List (List Ty)) → (L : Layout) →
    Slotted S K L → Slotted S K (fss.foldl (fun L fs => Layout.addTysWith S (fun L _ _ => L) L fs) L)
  | [], _, h => h
  | fs :: fss, L, h => slotted_fold hS fss _ (slotted_addTysWith hS (fun _ _ _ h => h) L h fs)

theorem effectSlots_kinds (S : Ty → Nat) {K L : Layout} (he : L.effects = K.effects) (ho : L.owns = K.owns) :
    Layout.effectSlots S L = Layout.effectSlots S K := by
  have : L.effectFields = K.effectFields := by
    funext e; simp [Layout.effectFields, Layout.effectsOf, Layout.ownsOf, he, ho]
  funext t
  unfold Layout.effectSlots
  split <;> simp [this]

/-- Every datatype `addTys` adds holds the slots its type gets, so a layout built from a layout without datatypes
gives each type the slots of the slot function. -/
theorem slotted_addTys {S : Ty → Nat} {L : Layout} (hS : NoSlots (Layout.effectSlots S L))
    (h : Slotted (Layout.effectSlots S L) L L) (ts : List Ty) :
    Slotted (Layout.effectSlots S L) L (Layout.addTys S L ts) := by
  unfold Layout.addTys
  refine slotted_addTysWith hS ?_ L h ts
  intro L' k a h'
  match k, a with
  | .effect, [e] =>
    show Slotted _ _ (Layout.addEffect (Layout.effectSlots S L') L' e)
    rw [effectSlots_kinds S h'.2.1 h'.2.2]
    exact slotted_push (slotted_fold hS _ _ h') _ _ (hS (.dsl .effect [e]) (by simp) (by simp) (by simp)).symm
  | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
  | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
  | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
  | .closure, _ | .effectClosure, _ | .fresh, _ => exact h'

theorem count_of_slotted {S : Ty → Nat} {K L : Layout} (h : Slotted S K L) {t : Ty} (hf : (L.find? t).isSome = true) :
    L.count t = S t := by
  obtain ⟨⟨d, n⟩, hx⟩ := Option.isSome_iff_exists.1 hf
  simp only [Layout.count, hx]
  simp only [Layout.find?, Option.map_eq_some_iff] at hx
  obtain ⟨⟨⟨u, m⟩, j⟩, hfind, he⟩ := hx
  cases he
  have hs := List.find?_some hfind
  simp only at hs
  have hu := eq_of_same hs
  subst hu
  exact h.1 _ (List.fst_mem_of_mem_zipIdx (List.mem_of_find?_eq_some hfind))

theorem stepSlots_plain (v : ServiceV) {t : Ty} (ht : ∀ k w, t ≠ .table k w) : stepSlots v t = boundSlots v.bounds t := by
  have : v.machines.any (fun m => (Ty.same m.table t).isSome) = false := by
    rw [List.any_eq_false]
    intro m _ h
    cases t with
    | table k w => exact ht k w rfl
    | _ => simp [MachineV.table, Ty.same] at h
  simp [stepSlots, this]

/-- A collection type the service's layout holds gets the slots of `stepSlots` (a list, its longest literal's). -/
theorem ofService_count {G : List Ty} (defs : Defs G) (v : ServiceV) {t : Ty}
    (hf : ((Layout.ofService defs v).find? t).isSome = true) :
    (Layout.ofService defs v).count t =
      Layout.effectSlots (listSlots (stepSlots v) defs.lits) (Layout.kindsOf defs.parts v) t := by
  have hS : NoSlots (Layout.effectSlots (listSlots (stepSlots v) defs.lits) (Layout.kindsOf defs.parts v)) := by
    intro t hb hl ht
    cases t with
    | bag u => exact absurd rfl (hb u)
    | list u => exact absurd rfl (hl u)
    | table k w => exact absurd rfl (ht k w)
    | _ => simp [Layout.effectSlots, listSlots, stepSlots_plain v ht, boundSlots]
  exact count_of_slotted (slotted_addTys hS (And.intro (fun p hp => nomatch hp) ⟨rfl, rfl⟩) _) hf

theorem stepSlots_table_ge (v : ServiceV) (k w : Ty) : boundSlots v.bounds (.table k w) ≤ stepSlots v (.table k w) := by
  unfold stepSlots; split <;> omega

/-- Every create's bound fits the slots of its table type in the service's layout, so asserting the creates of a
state loses no state within them. -/
theorem atMost_le_count {G : List Ty} (defs : Defs G) (v : ServiceV) {c : CreateV v.records} (hc : c ∈ v.bounds.creates)
    (hf : ((Layout.ofService defs v).find? (.table c.key c.value)).isSome = true) :
    c.atMostNat ≤ (Layout.ofService defs v).count (.table c.key c.value) := by
  rw [ofService_count defs v hf]
  exact Nat.le_trans (atMost_le_slots v.bounds c hc) (stepSlots_table_ge v _ _)

end Tazuna.Smt
