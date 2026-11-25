import Tazuna.Smt.EventPending
import Tazuna.Smt.ReactExact

/-! The effects an event's reactions start. A reaction returns a list of effects, coded as list slots in order. The
step starts them after the machines' effects, reactions in order and each reaction's effects in list order: a request
takes the next wire id, an own command or query the next place in the own queue. So a request slot's id is the id
after the requests before it, and an own slot's place the place after the own effects before it: running counts over
the slots gated by the variant test (`reactSlots`, `ownSlots`, `gateOwn`), linear in the slots. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {r e : Ty}

/-- The pending table slot of a request with the wire id `id`, the effect `eff` and the sender's key tuple items
`keyT`. Both items are shared, as moving the slot into the table copies them into every slot. -/
def pendingSlot (dE dP dk : Nat) (dflt : Term) (js : List Nat) (keyT : List Term) (f id eff : Term) : PendingSlot :=
  ⟨f, Term.share id, Term.share (entryT dE dP dk dflt keyT (Term.share eff) 0 js)⟩

/-- A reaction's effect slots as pending table slots, each occupied slot at the id `n` plus the occupied slots before
it, and the id after them. -/
def reactSlots (dE dP dk : Nat) (dflt : Term) (js : List Nat) : List (Slot 1) → Term → List PendingSlot × Term
  | [], n => ([], n)
  | (f, xs) :: S, n =>
    let rest := reactSlots dE dP dk dflt js S (Term.share (.add n (.ite f (.int 1) (.int 0))))
    (pendingSlot dE dP dk dflt js [] f n xs[0] :: rest.1, rest.2)

/-- The context a reaction reads: the records and the time. -/
def reactionCtxT (records now : Term) : Except Refusal Term :=
  adtCtor L 9 [r] [[r, .int]] 0 [records, now]

/-- Every reaction's effects on the event `ev`, reactions in order: the pending table slots of the requests from the
wire id `n` and the id after them, the own slots of the own commands and queries from the queue place `q` and the place
after them, and the condition. With no own kinds every effect is a request, and the list's slots are used as they
are. -/
def encodeReactions (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (dE dP : Nat) :
    List (ReactionV r e) → (records now ev n q : Term) → Except Refusal (List PendingSlot × Term × List OwnSlot × Term × Term)
  | [], _, _, _, n, q => pure ([], n, [], q, tt)
  | x :: xs, records, now, ev, n, q => do
    let (rc, c0) ← x.react.code L
    let cx ← Code.ofTermE _ (← reactionCtxT (r := r) L records now)
    let evc ← Code.ofTermE e ev
    let (l, c1) ← rc (cx, evc, ())
    let lt ← Code.termE _ l
    let (d, nl, dt) ← collD L (.list (.dsl .effect [e])) [.dsl .effect [e]]
    let (dk, _) ← L.findE (.tuple [])
    let js ← shapeIdxs shs ds ⟨[], .reaction x.name⟩ (L.effectsOf e)
    let dflt ← defaultE L (pendingEntry shs)
    let LS := slotsOf d dt nl 1 lt
    let none := (L.ownsOf e).isEmpty
    let gate (own : Bool) := gateOwn dE (L.effectsOf e).length (L.ownsOf e).length own LS
    let (S, n') := reactSlots dE dP dk dflt js (if none then LS else gate false) n
    let (O, q') := if none then ([], q) else ownSlots (gate true) q
    let (rest, n'', orest, q'', c2) ← encodeReactions shs ds dE dP xs records now ev n' q'
    pure (S ++ rest, n'', O ++ orest, q'', andT c0 (andT c1 c2))

end

section
variable {L : Layout} {M : Model} {e : Ty}

/-- T2 for a reaction's effect slots: the pending slots hold, where occupied, the requests for its effects in list
order at the ids from `n0`, and the id term after them denotes the id after them. -/
theorem reactSlots_rel {P : List AnySite} (hP : SitesUnique P) (name : String) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)} {js : List Nat}
    (hjs : shapeIdxs shs ds ⟨[], .reaction name⟩ (L.effectsOf e) = .ok js)
    {dE nE dP nP dk nk : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP)) (hdk : L.find? (.tuple []) = some (dk, nk)) (dflt : Term) :
    (S : List (Slot 1)) → (sv : List (Bool × List Val)) → (effs : List (EffectV e)) → SlotsDen M S sv →
    Holds2 (EBag L (.dsl .effect [e])) effs sv → (∀ x ∈ effs, x.Reach P) → (∀ x ∈ effs, x.isRequest = true) →
    {n : Term} → {n0 : Nat} →
    n.denote M = .int n0 →
    (reactSlots dE dP dk dflt js S n).2.denote M = .int ((n0 + effs.length : Nat) : Int) ∧
      NewsRel M L shs ds (reactSlots dE dP dk dflt js S n).1 (effs.map (Sender.reaction name, ·)) n0
  | [], [], effs, _, hh, _, _, n, n0, hn => by
    cases effs with
    | nil => exact ⟨by simpa [reactSlots] using hn, [], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩
    | cons _ _ => exact hh.elim
  | (f, xs) :: S, (b, vs) :: sv, effs, ⟨hf, hx, hS⟩, hh, hr, hrq, n, n0, hn => by
    have hl : (Term.denotes M (pendingSlot dE dP dk dflt js [] f n xs[0]).slot.2.1).length = 2 := by
      simp [pendingSlot, PendingSlot.slot, Term.denotes]
    cases b with
    | false =>
      have hn' : (Term.share (.add n (.ite f (.int 1) (.int 0)))).denote M = .int n0 := by
        simp [Term.denote_share, Term.denote, hn, hf, Val.toInt, Val.toBool]
      obtain ⟨h1, sv', zs, hS', hw, hh', xs', hp, hq⟩ :=
        reactSlots_rel hP name hshs hjs hE hPE hdk dflt S sv effs hS (by simpa [Holds2, occupied] using hh) hr hrq hn'
      refine ⟨h1, (false, _) :: sv', zs, ⟨hf, rfl, hS'⟩, ?_, by simpa [Holds2, occupied] using hh', xs', hp, hq⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hl, hw⟩
    | true =>
      match effs, hh with
      | x :: effs, ⟨⟨z, hz, hxz⟩, hh⟩ =>
        have hn' : (Term.share (.add n (.ite f (.int 1) (.int 0)))).denote M = .int ((n0 + 1 : Nat) : Int) := by
          simp [Term.denote_share, Term.denote, hn, hf, Val.toInt, Val.toBool]
        obtain ⟨h1, sv', zs, hS', hw, hh', xs', hp, hq⟩ :=
          reactSlots_rel hP name hshs hjs hE hPE hdk dflt S sv effs hS hh (fun y hy => hr y (by simp [hy]))
            (fun y hy => hrq y (by simp [hy])) hn'
        rw [hz] at hx
        obtain ⟨t, rfl⟩ := xs.one
        have ht : t.denote M = z := by simpa [Term.denotes] using hx
        obtain ⟨req, o, rfl, ho, y, hyrel, hpend⟩ := entry_rel (M := M) hP (.reaction name) hshs hjs hE hPE ()
          (keyT := []) ⟨dk, nk, [], hdk, rfl, rfl⟩ (hr x (by simp)) (hrq x (by simp)) (effT := Term.share t)
          (by rw [Term.denote_share, ht]; exact hxz) n0 dflt
        refine ⟨by show (reactSlots dE dP dk dflt js S _).2.denote M = _; rw [h1]; simp; omega, (true, _) :: sv',
          ((n0 : Nat), y) :: zs, ⟨hf, rfl, hS'⟩, ?_, ⟨⟨_, _, rfl, by simp only [pendingSlot, Term.denote_share]; exact hn, ?_⟩, hh'⟩,
          ((Sender.reaction name, .request req), n0) :: xs', ?_, ⟨⟨rfl, req, o, rfl, ho, hpend⟩, hq⟩⟩
        · simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨hl, hw⟩
        · simp only [pendingSlot, SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote_share]
          exact hyrel
        · simp only [List.map_cons, List.zipIdx_cons]
          exact hp.cons _
  | [], _ :: _, _, h, _, _, _, _, _, _ | _ :: _, [], _, h, _, _, _, _, _, _ => h.elim

end

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- The context of a reaction, read at the level codes relate to. -/
theorem up_rctx (h : (Ty.reactionCtx r).isData = true) (hrd : r.isData = true) (recs : r.den0) (now : Int) :
    Ty.up _ h (.inl (recs, now, ()) : (Ty.reactionCtx r).den0) =
      Alts.inj (vs := [[r, .int]]) ⟨0, by simp⟩ (Ty.up _ hrd recs, now, ()) := by
  refine (Ty.up_inl 9 [r] [r, .int] [] h (by simp [Ty.isData, Ty.isDatas, hrd]) _).trans ?_
  show Sum.inl _ = Sum.inl _
  congr 1
  refine (Ty.up_tuple _ _ _ hrd (by simp [Ty.isData, Ty.isDatas]) _).trans (congrArg _ ?_)
  exact (Ty.up_tuple _ _ _ rfl rfl _)

/-- The effects the reactions start on the event `ev`, reactions in order. -/
abbrev reactionEffects (xs : List (ReactionV r e)) (ev : e.den0) (recs : r.den0) (tnow : Int) :
    List (Sender × EffectV e) :=
  xs.flatMap fun x => (x.effectsAt ev recs tnow).map (.reaction x.name, ·)

/-- The arguments a reaction is applied to: its context and the event. -/
theorem react_args (x : ReactionV r e) (recs : r.den0) (tnow : Int) (ev : e.den0) (hrd : r.isData = true)
    (hed : e.isData = true) {records now evT ctxT : Term} (hrec : RelV L r (Ty.up _ hrd recs) (records.denote M))
    (hnow : now.denote M = .int tnow) (hev : RelV L e (Ty.up _ hed ev) (evT.denote M))
    (h2 : reactionCtxT (r := r) L records now = .ok ctxT) {cx : Code (Ty.reactionCtx r)} {evc : Code e}
    (h3 : Code.ofTerm? _ ctxT = some cx) (h4 : Code.ofTerm? e evT = some evc) :
    Smt.Rels M L [Ty.reactionCtx r, e] (Ty.up _ x.react.hps (.inl (recs, tnow, ()), ev, ())) (cx, evc, ()) := by
  have hps := x.react.hps
  have hcd : (Ty.reactionCtx r).isData = true := by
    simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at hps; exact hps.1
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[r, .int]]) ⟨0, by simp⟩ _ _ h2
    (Ty.up _ hrd recs, tnow, ()) ⟨_, _, rfl, hrec, _, _, rfl, hnow, rfl⟩
  rw [← up_rctx hcd hrd recs tnow] at hctx
  erw [Ty.up_tuple _ _ _ hcd (by simp [Ty.isData, Ty.isDatas, hed]), Ty.up_tuple _ _ _ hed rfl]
  exact ⟨(rel_ofTerm h3 _).2 hctx, (rel_ofTerm h4 _).2 hev, trivial⟩

/-- T2 for one reaction's effect list slots: the pending slots hold, where occupied, the requests among its effects in
list order at the ids from `n0`, and the own slots the own commands and queries at the places from `q0`; each term
after them denotes the id or place after them. -/
theorem reaction_parts {P : List AnySite} (hP : SitesUnique P) (name : String) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)} {js : List Nat}
    (hjs : shapeIdxs shs ds ⟨[], .reaction name⟩ (L.effectsOf e) = .ok js)
    {dE nE dP nP dk nk : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP)) (hdk : L.find? (.tuple []) = some (dk, nk)) (dflt : Term)
    {LS : List (Slot 1)} {sv : List (Bool × List Val)} {effs : List (EffectV e)} (hS : SlotsDen M LS sv)
    (hh : Holds2 (EBag L (.dsl .effect [e])) effs sv) (hr : ∀ x ∈ effs, x.Reach P) {n q : Term} {n0 q0 : Nat}
    (hn : n.denote M = .int n0) (hq : q.denote M = .int q0) :
    let gate (own : Bool) := gateOwn dE (L.effectsOf e).length (L.ownsOf e).length own LS
    let R := reactSlots dE dP dk dflt js (if (L.ownsOf e).isEmpty then LS else gate false) n
    let O := if (L.ownsOf e).isEmpty then ([], q) else ownSlots (gate true) q
    let effs' := effs.map (Sender.reaction name, ·)
    R.2.denote M = .int ((n0 + (Step.reqsOf effs').length : Nat) : Int) ∧ NewsRel M L shs ds R.1 (Step.reqsOf effs') n0 ∧
      O.2.denote M = .int ((q0 + (Step.queuedOf effs').length : Nat) : Int) ∧ OwnRel M L O.1 (Step.queuedOf effs') q0 := by
  intro gate R O effs'
  have hreq : Step.reqsOf effs' = (effs.filter (·.isRequest)).map (Sender.reaction name, ·) := by
    simp only [Step.reqsOf, effs', List.filter_map]; rfl
  have hqd : Step.queuedOf effs' = effs.filter (!·.isRequest) := by
    simp only [Step.queuedOf, effs', List.filter_map, List.map_map]
    exact List.map_id'' (fun _ => rfl) _
  rw [hreq, hqd]
  by_cases ho : (L.ownsOf e).isEmpty
  · have hall : ∀ x ∈ effs, x.isRequest = true := by
      intro x hx
      obtain ⟨vs, -, z, -, hz⟩ := forall2_mem_left hh _ hx
      exact request_of_rel (List.isEmpty_iff.1 ho) hz
    have h1 : effs.filter (·.isRequest) = effs := List.filter_eq_self.2 hall
    have h2 : effs.filter (!·.isRequest) = [] := List.filter_eq_nil_iff.2 fun x hx => by simp [hall x hx]
    simp only [R, O, ho, ↓reduceIte, h1, h2]
    obtain ⟨r1, r2⟩ := reactSlots_rel hP name hshs hjs hE hPE hdk dflt LS sv effs hS hh hr hall hn
    exact ⟨by simpa using r1, r2, by simpa using hq, ownRel_nil q0⟩
  · simp only [R, O, ho, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨sv1, hS1, hh1⟩ := gateOwn_rel (M := M) hE false LS sv effs hS hh
    obtain ⟨sv2, hS2, hh2⟩ := gateOwn_rel (M := M) hE true LS sv effs hS hh
    have e1 : (effs.filter fun x => false == !x.isRequest) = effs.filter (·.isRequest) := by
      congr 1; funext x; cases x.isRequest <;> rfl
    have e2 : (effs.filter fun x => true == !x.isRequest) = effs.filter (!·.isRequest) := by
      congr 1; funext x; cases x.isRequest <;> rfl
    replace hh1 := (congrArg (fun l : List (EffectV e) => Holds2 (EBag L (.dsl .effect [e])) l sv1) e1).mp hh1
    replace hh2 := (congrArg (fun l : List (EffectV e) => Holds2 (EBag L (.dsl .effect [e])) l sv2) e2).mp hh2
    obtain ⟨r1, r2⟩ := reactSlots_rel hP name hshs hjs hE hPE hdk dflt _ sv1 _ hS1 hh1
      (fun x hx => hr x (List.mem_filter.1 hx).1) (fun x hx => (List.mem_filter.1 hx).2) hn
    obtain ⟨o1, o2⟩ := ownSlots_rel _ sv2 _ hS2 hh2 hq
    exact ⟨by simpa using r1, r2, o1, o2⟩

/-- The reactions' effects: the condition holds exactly when every reaction's kept source fits and its application
to the event fits, and wherever it holds the pending slots hold, where occupied, the requests among the reactions'
effects in the step's order at the ids from `n0`, and the own slots the own commands and queries at the places from
`q0`; each term after them denotes the id or place after them. -/
theorem reactions_encode {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    {dE nE dP nP : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (recs : r.den0) (tnow : Int) (ev : e.den0) (hrd : r.isData = true) (hed : e.isData = true)
    {records now evT : Term} (hrec : RelV L r (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hev : RelV L e (Ty.up _ hed ev) (evT.denote M)) :
    (xs : List (ReactionV r e)) → (∀ x ∈ xs, x.Reach P) → {n q : Term} → {news : List PendingSlot} → {n' : Term} →
    {owns : List OwnSlot} → {q' c : Term} →
    encodeReactions L shs ds dE dP xs records now evT n q = .ok (news, n', owns, q', c) →
    (Holds M c ↔ ∀ x ∈ xs, (x.react.fits L.count).1 ∧ x.react.appFits L.count (.inl (recs, tnow, ()), ev, ())) ∧
    (∀ {n0 q0 : Nat}, n.denote M = .int n0 → q.denote M = .int q0 → Holds M c →
      n'.denote M = .int ((n0 + (Step.reqsOf (reactionEffects xs ev recs tnow)).length : Nat) : Int) ∧
      NewsRel M L shs ds news (Step.reqsOf (reactionEffects xs ev recs tnow)) n0 ∧
      q'.denote M = .int ((q0 + (Step.queuedOf (reactionEffects xs ev recs tnow)).length : Nat) : Int) ∧
      OwnRel M L owns (Step.queuedOf (reactionEffects xs ev recs tnow)) q0)
  | [], _, n, q, news, n', owns, q', c, henc => by
    simp only [encodeReactions, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := henc
    exact ⟨by simp [holds_tt], fun hn hq _ => ⟨by simpa using hn,
      ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩, by simpa using hq,
      ownRel_nil _⟩⟩
  | x :: xs, hreach, n, q, news, n', owns, q', c, henc => by
    obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨ctxT, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨cx, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨evc, h4, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨l, c1⟩, h5, henc⟩ := bind_ok.1 henc
    obtain ⟨lt, h6, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨d, nl, dt⟩, h7, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨dk, nk⟩, h8, henc⟩ := bind_ok.1 henc
    obtain ⟨js, h9, henc⟩ := bind_ok.1 henc
    obtain ⟨dflt, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, n'', orest, q'', c2⟩, h10, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have IH := reactions_encode hP hshs hE hPE recs tnow ev hrd hed hrec hnow hev xs
      (fun y hy => hreach y (by simp [hy])) h10
    refine ⟨?_, fun {n0 q0} hn hq hc => ?_⟩
    · have e0 := (x.react.code_exact (M := M) h1).1
      have e1 : ∀ hc0 : Holds M c0, (Holds M c1 ↔ x.react.appFits L.count (.inl (recs, tnow, ()), ev, ())) := fun hc0 =>
        x.react.app_exact h1 hc0 (fun t ht => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact ofTerm_notFn (need_ok.1 h3)
          · exact ofTerm_notFn (need_ok.1 h4)) _ _
          (react_args x recs tnow ev hrd hed hrec hnow hev h2 (need_ok.1 h3) (need_ok.1 h4)) h5
      rw [holds_andT, holds_andT, e0, IH.1]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨p0, p1, p2⟩
        exact ⟨⟨p0, (e1 (e0.2 p0)).1 p1⟩, p2⟩
      · rintro ⟨⟨p0, p1⟩, p2⟩
        exact ⟨p0, (e1 (e0.2 p0)).2 p1, p2⟩
    obtain ⟨hc0, hc12⟩ := (holds_andT _ _).1 hc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc12
    have hl := x.react.code_apply h1 hc0 _ _ (react_args x recs tnow ev hrd hed hrec hnow hev h2 (need_ok.1 h3)
      (need_ok.1 h4)) h5 hc1
    obtain rfl : l = lt := Option.some.inj (need_ok.1 h6)
    obtain ⟨sv, hS, -, -, hh⟩ := list_view hl h7
    have hr1 := ReactionV.reach_effectsAt P x (hreach x (by simp)) ev recs tnow
    obtain ⟨hn1, hnews1, hq1, hown1⟩ := reaction_parts hP x.name hshs h9 hE hPE (need_ok.1 h8) dflt (effs := x.effectsAt ev recs tnow) hS hh hr1 hn hq
    obtain ⟨hn2, hnews2, hq2, hown2⟩ := IH.2 hn1 hq1 hc2
    have hfl : ∀ a b : List (Sender × EffectV e), Step.reqsOf (a ++ b) = Step.reqsOf a ++ Step.reqsOf b ∧
        Step.queuedOf (a ++ b) = Step.queuedOf a ++ Step.queuedOf b := fun _ _ => by
      simp [Step.reqsOf, Step.queuedOf, List.filter_append]
    simp only [reactionEffects, List.flatMap_cons] at hn2 hnews2 hq2 hown2 ⊢
    rw [(hfl _ _).1, (hfl _ _).2]
    refine ⟨?_, newsRel_append hnews1 hnews2, ?_, ownRel_append hown1 hown2⟩
    · rw [hn2, List.length_append]; congr 2; omega
    · rw [hq2, List.length_append]; congr 2; omega

end

end Tazuna.Smt
