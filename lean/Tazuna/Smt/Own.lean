import Tazuna.Smt.Starts

/-! Own commands and queries among the effects a step starts. A request goes out at once with the next wire id; an
own command or query waits in the own queue and runs later as an internal step, in the order the step started it
(`Step.start`). The effect datatype codes the request kinds first and the own kinds after them, so a term tells an own
effect by its variant (`isOwnT`). Each place where effects start splits its slots by that test: the requests' slots
are the ones the pending write reads, and the own slots hold each own effect with its place in the queue (`OwnRel`),
numbered as wire ids are. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Whether the effect value `t` of the effect datatype `dE` is an own command or query: one of the `nO` variants
after the `nR` request variants. -/
def isOwnT (dE nR nO : Nat) (t : Term) : Term := anyT ((List.range nO).map fun k => .is dE (nR + k) t)

/-- A start slot (flag, key, effect option) split in two: the first keeps the option where it holds a request, the
second where it holds an own command or query; each reads none elsewhere. -/
def splitStart (dE nR nO dopt : Nat) (w : Term × Term × Term) : (Term × Term × Term) × (Term × Term × Term) :=
  let own := Term.share (isOwnT dE nR nO (.sel dopt 0 0 w.2.2))
  ((w.1, w.2.1, Term.share (.ite own (.ctor dopt 1 []) w.2.2)), (w.1, w.2.1, Term.share (.ite own w.2.2 (.ctor dopt 1 []))))

/-- The own slots of start slots ranked like wire ids: each flagged slot holds its place in the queue and its effect. -/
def ownItems (S : List Slot) : List Slot := S.map fun (f, xs) => (f, [xs.headD tt, xs.getD 2 tt])

/-- A list's effect slots as own slots, each occupied slot at the place `q` plus the occupied slots before it, and the
place after them. -/
def ownSlots : List Slot → Term → List Slot × Term
  | [], q => ([], q)
  | (f, xs) :: S, q =>
    let rest := ownSlots S (Term.share (.add q (.ite f (.int 1) (.int 0))))
    ((f, [q, xs.headD tt]) :: rest.1, rest.2)

/-- The slots with each flag and-ed with whether its effect is a request (`own` false) or an own command or query. -/
def gateOwn (dE nR nO : Nat) (own : Bool) (S : List Slot) : List Slot :=
  S.map fun (f, xs) => let o := isOwnT dE nR nO (xs.headD tt); (Term.share (.and f (if own then o else .not o)), xs)

/-- The own effect at the queue place `k`: whether a flagged own slot holds that place, and its effect (`dflt`, any
term of the effect's sort, where none does). An internal step runs the own effect at its place. -/
def queueAt (dflt : Term) (S : List Slot) (k : Term) : Term × Term :=
  (anyT (S.map fun (f, xs) => .and f (.eq (xs.headD tt) k)),
    pickT dflt (S.map fun (f, xs) => (f, .eq (xs.headD tt) k, xs.getD 1 tt)))

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- An own command or query with its place in the queue, and its own slot's items. -/
def EOwn (L : Layout) (e : Ty) : EffectV e × Nat → List Val → Prop :=
  fun x vs => ∃ zx, vs = [.int (x.2 : Int), zx] ∧ RelV L (.dsl .effect [e]) x.1 zx

/-- The own slots hold, where flagged, the own commands and queries `os` with their places in the queue from `q0`, in
some order. -/
def OwnRel (M : Model) (L : Layout) (S : List Slot) (os : List (EffectV e)) (q0 : Nat) : Prop :=
  ∃ sv zs, SlotsDen M S sv ∧ (∀ p ∈ sv, p.2.length = 2) ∧ Holds2 (EOwn L e) zs sv ∧ zs.Perm (os.zipIdx q0)

/-- The variant test reads whether an effect is an own command or query. -/
theorem isOwn_den {dE nE : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE)) {x : EffectV e} {t : Term}
    (h : RelV L (.dsl .effect [e]) x (t.denote M)) :
    (isOwnT dE (L.effectsOf e).length (L.ownsOf e).length t).denote M = .bool (!x.isRequest) := by
  obtain ⟨d, n, hd, ⟨k, key, vals, hk, hz, hh⟩ | ⟨k, key, vals, hk, hz, hh⟩⟩ := h
  · obtain rfl : dE = d := find_det hE hd
    have hlt : k < (L.effectsOf e).length := (List.getElem?_eq_some_iff.1 hk).1
    cases x with
    | request =>
      simp only [isOwnT, anyT_denote, List.any_map, Function.comp_def, Term.denote, hz, Val.toBool,
        EffectV.isRequest, Bool.not_true]
      congr 1
      rw [List.any_eq_false]
      intro j _
      simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq]
      omega
    | command => exact hh.elim
    | query => exact hh.elim
  · obtain rfl : dE = d := find_det hE hd
    have hlt : k < (L.ownsOf e).length := (List.getElem?_eq_some_iff.1 hk).1
    have hnr : x.isRequest = false := by
      cases x with
      | request => cases key <;> exact hh.elim
      | command => rfl
      | query => rfl
    simp only [isOwnT, anyT_denote, List.any_map, Function.comp_def, Term.denote, hz, Val.toBool, hnr,
      Bool.not_false]
    congr 1
    rw [List.any_eq_true]
    exact ⟨k, List.mem_range.2 hlt, by simp⟩

/-- With no own kinds every effect value the layout codes is a request. -/
theorem request_of_rel (ho : L.ownsOf e = []) {x : EffectV e} {z : Val} (h : RelV L (.dsl .effect [e]) x z) :
    x.isRequest = true := by
  obtain ⟨d, n, hd, ⟨k, key, vals, hk, hz, hh⟩ | ⟨k, key, vals, hk, -, -⟩⟩ := h
  · cases x with
    | request => rfl
    | command => exact hh.elim
    | query => exact hh.elim
  · rw [ho] at hk; cases hk

theorem ownRel_nil (q0 : Nat) : OwnRel M L [] ([] : List (EffectV e)) q0 :=
  ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], by simp⟩

theorem ownRel_append {S S' : List Slot} {os os' : List (EffectV e)} {q0 : Nat} (h : OwnRel M L S os q0)
    (h' : OwnRel M L S' os' (q0 + os.length)) : OwnRel M L (S ++ S') (os ++ os') q0 := by
  obtain ⟨sv, zs, hS, hw, hh, hp⟩ := h
  obtain ⟨sv', zs', hS', hw', hh', hp'⟩ := h'
  refine ⟨sv ++ sv', zs ++ zs', slotsDen_append hS hS', ?_, ?_, ?_⟩
  · intro p hp; rcases List.mem_append.1 hp with hp | hp
    · exact hw p hp
    · exact hw' p hp
  · unfold Holds2 at *; rw [occupied_append]; exact forall2_append hh hh'
  · rw [List.zipIdx_append]; exact hp.append hp'

/-- The effect option keeping only a request. -/
def optReq : (Ty.option (.dsl .effect [e])).den → (Ty.option (.dsl .effect [e])).den
  | .inl (x, ()) => if x.isRequest then .inl (x, ()) else .inr (.inl ())
  | o => o

/-- The effect option keeping only an own command or query. -/
def optOwn : (Ty.option (.dsl .effect [e])).den → (Ty.option (.dsl .effect [e])).den
  | .inl (x, ()) => if x.isRequest then .inr (.inl ()) else .inl (x, ())
  | o => o

/-- The two halves of a split start slot hold the request and the own part of its effect option. -/
theorem splitStart_rel {dE nE dopt nopt : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)) {v : (Ty.option (.dsl .effect [e])).den}
    (w : Term × Term × Term) (h : RelV L (Ty.option (.dsl .effect [e])) v (w.2.2.denote M)) :
    RelV L (Ty.option (.dsl .effect [e])) (optReq v)
        ((splitStart dE (L.effectsOf e).length (L.ownsOf e).length dopt w).1.2.2.denote M) ∧
      RelV L (Ty.option (.dsl .effect [e])) (optOwn v)
        ((splitStart dE (L.effectsOf e).length (L.ownsOf e).length dopt w).2.2.2.denote M) := by
  rcases opt_view hopt h with ⟨x, zx, rfl, hz, hx⟩ | ⟨rfl, hz⟩
  · have hsel : (Term.sel dopt 0 0 w.2.2).denote M = zx := by simp [Term.denote, hz]
    have hown := isOwn_den (M := M) hE (t := .sel dopt 0 0 w.2.2) (by rw [hsel]; exact hx)
    cases hr : x.isRequest
    · simp only [splitStart, Term.denote_share, Term.denote, hown, hr, Bool.not_false, Val.toBool, 
        optReq, optOwn, Bool.false_eq_true]
      exact ⟨none_rel hopt, h⟩
    · simp only [splitStart, Term.denote_share, Term.denote, hown, hr, Bool.not_true, Val.toBool,
        ite_false, optReq, optOwn, Bool.false_eq_true]
      exact ⟨h, none_rel hopt⟩
  · have hn : ∀ c : Term, (Term.ite c (.ctor dopt 1 []) w.2.2).denote M = .ctor dopt 1 [] ∧
        (Term.ite c w.2.2 (.ctor dopt 1 [])).denote M = .ctor dopt 1 [] := by
      intro c; constructor <;> (simp only [Term.denote]; split <;> simp [hz, Term.denotes])
    simp only [splitStart, Term.denote_share, (hn _).1, (hn _).2, optReq, optOwn]
    exact ⟨none_rel hopt, none_rel hopt⟩

theorem toList_optReq (f : EffectV e → Sender × EffectV e) (hf : ∀ x, (f x).2 = x) :
    (o : (Ty.option (.dsl .effect [e])).den) →
    ((Ty.toOption (optReq o)).map f).toList = ((Ty.toOption o).map f).toList.filter (·.2.isRequest)
  | .inl (x, ()) => by
    have h1 : ((Ty.toOption (.inl (x, ()) : (Ty.option (.dsl .effect [e])).den)).map f).toList = [f x] := rfl
    have h0 : ((Ty.toOption (.inr (.inl ()) : (Ty.option (.dsl .effect [e])).den)).map f).toList = [] := rfl
    have hp : (f x).2.isRequest = x.isRequest := congrArg EffectV.isRequest (hf x)
    cases hx : x.isRequest
    · rw [h1]
      simp only [optReq, hx, Bool.false_eq_true, ↓reduceIte]
      exact h0.trans (by simp [hp, hx])
    · rw [h1]
      simp only [optReq, hx, ↓reduceIte]
      exact h1.trans (by simp [hp, hx])
  | .inr (.inl ()) => rfl

theorem toList_optOwn (f : EffectV e → Sender × EffectV e) (hf : ∀ x, (f x).2 = x) :
    (o : (Ty.option (.dsl .effect [e])).den) →
    ((Ty.toOption (optOwn o)).map f).toList = ((Ty.toOption o).map f).toList.filter (!·.2.isRequest)
  | .inl (x, ()) => by
    have h1 : ((Ty.toOption (.inl (x, ()) : (Ty.option (.dsl .effect [e])).den)).map f).toList = [f x] := rfl
    have h0 : ((Ty.toOption (.inr (.inl ()) : (Ty.option (.dsl .effect [e])).den)).map f).toList = [] := rfl
    have hp : (f x).2.isRequest = x.isRequest := congrArg EffectV.isRequest (hf x)
    cases hx : x.isRequest
    · rw [h1]
      simp only [optOwn, hx, Bool.false_eq_true, ↓reduceIte]
      exact h1.trans (by simp [hp, hx])
    · rw [h1]
      simp only [optOwn, hx, ↓reduceIte]
      exact h0.trans (by simp [hp, hx])
  | .inr (.inl ()) => rfl

theorem sentBy_optReq (m : MachineV r e) {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
    (a : α) : (sentBy m κ (fun a => optReq (F a)) a).toList = (sentBy m κ F a).toList.filter (·.2.isRequest) :=
  toList_optReq _ (fun _ => rfl) (F a)

theorem sentBy_optOwn (m : MachineV r e) {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
    (a : α) : (sentBy m κ (fun a => optOwn (F a)) a).toList = (sentBy m κ F a).toList.filter (!·.2.isRequest) :=
  toList_optOwn _ (fun _ => rfl) (F a)

/-- Start slots whose effect options a term map rewrites, as `G` rewrites the options' values. -/
theorem startSlots_map (m : MachineV r e) {α : Type} {κ : α → m.key.den0} {F : α → (Ty.option (.dsl .effect [e])).den}
    (G : (Ty.option (.dsl .effect [e])).den → (Ty.option (.dsl .effect [e])).den) (g : Term × Term × Term → Term)
    (hg : ∀ v w, RelV L (Ty.option (.dsl .effect [e])) v (w.2.2.denote M) →
      RelV L (Ty.option (.dsl .effect [e])) (G v) ((g w).denote M)) :
    (ws : List (Term × Term × Term)) → (sv : List (Bool × List Val)) → (E : List α) →
    SlotsDen M (ws.map fun w => (w.1, [w.2.1, w.2.2])) sv → Holds2 (EOpt (L := L) m κ F) E sv →
    ∃ sv', SlotsDen M (ws.map fun w => (w.1, [w.2.1, g w])) sv' ∧ Holds2 (EOpt (L := L) m κ fun a => G (F a)) E sv'
  | [], [], E, _, hE => by
    cases E with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons _ _ => exact hE.elim
  | w :: ws, (b, vs) :: sv, E, ⟨hf, hvs, hS⟩, hE => by
    have hden : ∀ x y : Term, Term.denotes M [x, y] = [x.denote M, y.denote M] := fun _ _ => rfl
    cases b with
    | false =>
      obtain ⟨sv', hS', hh'⟩ := startSlots_map m G g hg ws sv E hS (by simpa [Holds2, occupied] using hE)
      exact ⟨(false, _) :: sv', ⟨hf, rfl, hS'⟩, by simpa [Holds2, occupied] using hh'⟩
    | true =>
      match E, hE with
      | a :: E, ⟨⟨zk, z, hz, hk, hv⟩, hE⟩ =>
        obtain ⟨sv', hS', hh'⟩ := startSlots_map m G g hg ws sv E hS hE
        rw [hden] at hvs
        rw [← hvs] at hz
        simp only [List.cons.injEq, and_true] at hz
        refine ⟨(true, [w.2.1.denote M, (g w).denote M]) :: sv', ⟨hf, rfl, hS'⟩,
          ⟨_, _, rfl, by rw [hz.1]; exact hk, hg _ w (by rw [hz.2]; exact hv)⟩, hh'⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-- An effect list's slots gated by the variant test hold, where occupied, the requests (`own` false) or the own
commands and queries among the effects, in order. -/
theorem gateOwn_rel {dE nE : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE)) (own : Bool) :
    (S : List Slot) → (sv : List (Bool × List Val)) → (effs : List (EffectV e)) → SlotsDen M S sv →
    Holds2 (EBag L (.dsl .effect [e])) effs sv →
    ∃ sv', SlotsDen M (gateOwn dE (L.effectsOf e).length (L.ownsOf e).length own S) sv' ∧
      Holds2 (EBag L (.dsl .effect [e])) (effs.filter fun x => own == !x.isRequest) sv'
  | [], [], effs, _, hh => by
    cases effs with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons _ _ => exact hh.elim
  | (f, xs) :: S, (b, vs) :: sv, effs, ⟨hf, hx, hS⟩, hh => by
    cases b with
    | false =>
      obtain ⟨sv', h1, h2⟩ := gateOwn_rel hE own S sv effs hS (by simpa [Holds2, occupied] using hh)
      refine ⟨(false, vs) :: sv', ⟨by simp [Term.denote, hf, Val.toBool], hx, h1⟩, by simpa [Holds2, occupied] using h2⟩
    | true =>
      match effs, hh with
      | x :: effs, ⟨⟨z, hz, hxz⟩, hh⟩ =>
        obtain ⟨sv', h1, h2⟩ := gateOwn_rel hE own S sv effs hS hh
        rw [hz] at hx
        obtain ⟨t, rfl, ht⟩ : ∃ t, xs = [t] ∧ t.denote M = z := by
          match xs, hx with
          | [t], hx => simp only [Term.denotes, List.cons.injEq, and_true] at hx; exact ⟨t, rfl, hx⟩
        have ho := isOwn_den (M := M) hE (t := t) (by rw [ht]; exact hxz)
        refine ⟨(own == !x.isRequest, [z]) :: sv', ⟨?_, by simp [Term.denotes, ht], h1⟩, ?_⟩
        · cases own <;> simp [Term.denote, hf, ho, Val.toBool]
        · cases hp : (own == !x.isRequest)
          · have hfl : (x :: effs).filter (fun x => own == !x.isRequest) = effs.filter (fun x => own == !x.isRequest) :=
              List.filter_cons_of_neg (by simp [hp])
            show Forall2 _ ((x :: effs).filter (fun x => own == !x.isRequest)) _
            rw [hfl]
            exact h2
          · have hfl : (x :: effs).filter (fun x => own == !x.isRequest) =
                x :: effs.filter (fun x => own == !x.isRequest) := List.filter_cons_of_pos (by simp [hp])
            show Forall2 _ ((x :: effs).filter (fun x => own == !x.isRequest)) _
            rw [hfl]
            exact ⟨⟨z, rfl, hxz⟩, h2⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-- T2 for an effect list's own slots: the own slots hold, where occupied, the effects in list order at the places from
`q0`, and the place term after them denotes the place after them. -/
theorem ownSlots_rel : (S : List Slot) → (sv : List (Bool × List Val)) → (os : List (EffectV e)) → SlotsDen M S sv →
    Holds2 (EBag L (.dsl .effect [e])) os sv → {q : Term} → {q0 : Nat} → q.denote M = .int q0 →
    (ownSlots S q).2.denote M = .int ((q0 + os.length : Nat) : Int) ∧ OwnRel M L (ownSlots S q).1 os q0
  | [], [], os, _, hh, q, q0, hq => by
    cases os with
    | nil => exact ⟨by simpa [ownSlots] using hq, ownRel_nil q0⟩
    | cons _ _ => exact hh.elim
  | (f, xs) :: S, (b, vs) :: sv, os, ⟨hf, hx, hS⟩, hh, q, q0, hq => by
    have hl : (Term.denotes M [q, xs.headD tt]).length = 2 := rfl
    cases b with
    | false =>
      have hq' : (Term.share (.add q (.ite f (.int 1) (.int 0)))).denote M = .int q0 := by
        simp [Term.denote_share, Term.denote, hq, hf, Val.toInt, Val.toBool]
      obtain ⟨h1, sv', zs, hS', hw, hh', hp⟩ := ownSlots_rel S sv os hS (by simpa [Holds2, occupied] using hh) hq'
      refine ⟨h1, (false, _) :: sv', zs, ⟨hf, rfl, hS'⟩, ?_, by simpa [Holds2, occupied] using hh', hp⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hl, hw⟩
    | true =>
      match os, hh with
      | x :: os, ⟨⟨z, hz, hxz⟩, hh⟩ =>
        have hq' : (Term.share (.add q (.ite f (.int 1) (.int 0)))).denote M = .int ((q0 + 1 : Nat) : Int) := by
          simp [Term.denote_share, Term.denote, hq, hf, Val.toInt, Val.toBool]
        obtain ⟨h1, sv', zs, hS', hw, hh', hp⟩ := ownSlots_rel S sv os hS hh hq'
        rw [hz] at hx
        obtain ⟨t, rfl, ht⟩ : ∃ t, xs = [t] ∧ t.denote M = z := by
          match xs, hx with
          | [t], hx => simp only [Term.denotes, List.cons.injEq, and_true] at hx; exact ⟨t, rfl, hx⟩
        refine ⟨by show (ownSlots S _).2.denote M = _; rw [h1]; simp; omega, (true, _) :: sv', (x, q0) :: zs,
          ⟨hf, rfl, hS'⟩, ?_, ⟨⟨z, by simp [Term.denotes, hq, ht], hxz⟩, hh'⟩, ?_⟩
        · simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨hl, hw⟩
        · simp only [List.zipIdx_cons]
          exact hp.cons _
  | [], _ :: _, _, h, _, _, _, _ | _ :: _, [], _, h, _, _, _, _ => h.elim

theorem queueAt_slots (dflt : Term) {k : Term} {K : Int} (hk : k.denote M = .int K) :
    (S : List Slot) → (sv : List (Bool × List Val)) → (zs : List (EffectV e × Nat)) → SlotsDen M S sv →
    Holds2 (EOwn L e) zs sv →
    ((S.map fun (f, xs) => Term.and f (.eq (xs.headD tt) k)).any fun t => (t.denote M).toBool) =
        (zs.any fun z => (z.2 : Int) == K) ∧
      ∀ z, zs.find? (fun z => (z.2 : Int) == K) = some z →
        RelV L (.dsl .effect [e]) z.1 ((pickT dflt (S.map fun (f, xs) => (f, .eq (xs.headD tt) k, xs.getD 1 tt))).denote M)
  | [], [], zs, _, hh => by
    cases zs with
    | nil => exact ⟨rfl, fun z h => by simp at h⟩
    | cons _ _ => exact hh.elim
  | (f, xs) :: S, (b, vs) :: sv, zs, ⟨hf, hx, hS⟩, hh => by
    have hand : ∀ h : Term, (Term.and f h).denote M = .bool (b && (h.denote M).toBool) := fun h => by
      show Val.bool ((f.denote M).toBool && (h.denote M).toBool) = _
      rw [hf]; rfl
    have hpick : ∀ h r rest, (pickT dflt ((f, h, r) :: rest)).denote M =
        if b && (h.denote M).toBool then r.denote M else (pickT dflt rest).denote M := fun h r rest => by
      show (if ((Term.and f h).denote M).toBool then _ else _) = _
      rw [hand]; rfl
    cases b with
    | false =>
      obtain ⟨h1, h2⟩ := queueAt_slots dflt hk S sv zs hS (by simpa [Holds2, occupied] using hh)
      refine ⟨?_, fun z hz => ?_⟩
      · simp only [List.map_cons, List.any_cons, hand, Val.toBool, Bool.false_and, Bool.false_or]
        exact h1
      · simp only [List.map_cons, hpick, Bool.false_and]
        exact h2 z hz
    | true =>
      match zs, hh with
      | z :: zs, ⟨⟨zx, hz, hzx⟩, hh⟩ =>
        obtain ⟨h1, h2⟩ := queueAt_slots dflt hk S sv zs hS hh
        rw [← hx] at hz
        obtain ⟨a, c, rfl, ha, hc⟩ : ∃ a c, xs = [a, c] ∧ a.denote M = .int (z.2 : Int) ∧ c.denote M = zx := by
          match xs, hz with
          | [a, c], hz =>
            simp only [Term.denotes, List.cons.injEq, and_true] at hz
            exact ⟨a, c, rfl, hz.1, hz.2⟩
          | [], hz | [_], hz | _ :: _ :: _ :: _, hz => simp [Term.denotes] at hz
        have hhit : (Term.eq a k).denote M = .bool ((z.2 : Int) == K) := by
          show Val.bool (a.denote M == k.denote M) = _
          rw [ha, hk]; rfl
        refine ⟨?_, fun z' hz' => ?_⟩
        · simp only [List.map_cons, List.any_cons, hand, List.headD_cons, hhit, Val.toBool, Bool.true_and]
          congr 1
        · simp only [List.map_cons, hpick, List.headD_cons, hhit, Val.toBool, Bool.true_and]
          cases hq : ((z.2 : Int) == K)
          · simp only [List.find?_cons, hq] at hz'
            exact h2 z' hz'
          · simp only [List.find?_cons, hq, Option.some.injEq] at hz'
            subst hz'
            simp only [ite_true, List.getD_cons_succ, List.getD_cons_zero, hc]
            exact hzx
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-- T2 for the queue's head at place `q0 + i`: a flagged own slot holds that place exactly when the queue has an `i`-th
own effect, and then the effect term denotes it. -/
theorem queueAt_rel (dflt : Term) {S : List Slot} {os : List (EffectV e)} {q0 : Nat} (h : OwnRel M L S os q0)
    {k : Term} (i : Nat) (hk : k.denote M = .int ((q0 + i : Nat) : Int)) :
    (queueAt dflt S k).1.denote M = .bool (decide (i < os.length)) ∧
      ∀ hi : i < os.length, RelV L (.dsl .effect [e]) os[i] ((queueAt dflt S k).2.denote M) := by
  obtain ⟨sv, zs, hS, -, hh, hp⟩ := h
  obtain ⟨h1, h2⟩ := queueAt_slots dflt hk S sv zs hS hh
  have h1' : (queueAt dflt S k).1.denote M = .bool (zs.any fun z => (z.2 : Int) == ((q0 + i : Nat) : Int)) := by
    rw [← h1]; exact anyT_denote _
  have hplace : ∀ z ∈ zs, (z.2 : Int) = ((q0 + i : Nat) : Int) → ∃ hi : i < os.length, z = (os[i], q0 + i) := by
    intro z hz he
    have hm := hp.mem_iff.1 hz
    obtain ⟨x, j⟩ := z
    have he' : j = q0 + i := by exact_mod_cast he
    subst he'
    obtain ⟨-, hlt, hx⟩ := List.mem_zipIdx hm
    refine ⟨by omega, ?_⟩
    rw [hx]
    simp
  refine ⟨?_, fun hi => ?_⟩
  · rw [h1']
    congr 1
    by_cases hi : i < os.length
    · rw [decide_eq_true hi, List.any_eq_true]
      refine ⟨(os[i], q0 + i), hp.symm.mem_iff.1 ?_, by simp⟩
      exact List.mk_mem_zipIdx_iff_le_and_getElem?_sub.2 ⟨by omega, by simp [List.getElem?_eq_getElem hi]⟩
    · rw [decide_eq_false hi, List.any_eq_false]
      intro z hz he
      obtain ⟨hi', -⟩ := hplace z hz (by simpa using he)
      exact hi hi'
  · have hin : (os[i], q0 + i) ∈ zs := hp.symm.mem_iff.1
      (List.mk_mem_zipIdx_iff_le_and_getElem?_sub.2 ⟨by omega, by simp [List.getElem?_eq_getElem hi]⟩)
    obtain ⟨z, hz⟩ : ∃ z, zs.find? (fun z => (z.2 : Int) == ((q0 + i : Nat) : Int)) = some z :=
      Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨_, hin, by simp⟩)
    obtain ⟨_, hzeq⟩ := hplace z (List.mem_of_find?_eq_some hz) (by simpa using List.find?_some hz)
    have := h2 z hz
    rw [hzeq] at this
    exact this

end

end Tazuna.Smt
