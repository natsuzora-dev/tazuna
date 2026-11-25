import Tazuna.Smt.EventPending
import Tazuna.Smt.ReactExact

/-! The requests an event's reactions start. A reaction returns a list of effects, coded as list slots in order; every
effect value the layout codes is a request, so each occupied slot is written into the pending table. The step starts
them after the machines' effects, reactions in order and each reaction's effects in list order, so a slot's wire id is
the id after the effects before it: a running count over the slots (`reactSlots`), linear in the slots. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {r e : Ty}

/-- The pending table slot of a request with the wire id `id`, the effect `eff` and the sender's key tuple items
`keyT`. Both items are shared, as moving the slot into the table copies them into every slot. -/
def pendingItems (dE dP dk : Nat) (dflt : Term) (js : List Nat) (keyT : List Term) (id eff : Term) : List Term :=
  [Term.share id, Term.share (entryT dE dP dk dflt keyT (Term.share eff) 0 js)]

/-- A reaction's effect slots as pending table slots, each occupied slot at the id `n` plus the occupied slots before
it, and the id after them. -/
def reactSlots (dE dP dk : Nat) (dflt : Term) (js : List Nat) : List Slot → Term → List Slot × Term
  | [], n => ([], n)
  | (f, xs) :: S, n =>
    let rest := reactSlots dE dP dk dflt js S (Term.share (.add n (.ite f (.int 1) (.int 0))))
    ((f, pendingItems dE dP dk dflt js [] n (xs.headD tt)) :: rest.1, rest.2)

/-- The context a reaction reads: the records and the time. -/
def reactionCtxT (records now : Term) : Except Refusal Term :=
  adtCtor L 9 [r] [[r, .int]] 0 [records, now]

/-- Every reaction's requests on the event `ev`, reactions in order, from the wire id `n`: their pending table slots,
the id after them and the condition. -/
def encodeReactions (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (dE dP : Nat) :
    List (ReactionV r e) → (records now ev n : Term) → Except Refusal (List Slot × Term × Term)
  | [], _, _, _, n => pure ([], n, tt)
  | x :: xs, records, now, ev, n => do
    let (rc, c0) ← x.react.code L
    let cx ← need "a context that has no term" (Code.ofTerm? _ (← reactionCtxT (r := r) L records now))
    let evc ← need "an event that has no term" (Code.ofTerm? e ev)
    let (l, c1) ← rc (cx, evc, ())
    let lt ← need "a list that has no term" (Code.term? _ l)
    let (d, nl, dt) ← collD L (.list (.dsl .effect [e])) [.dsl .effect [e]]
    let (dk, _) ← need "a layout without the empty key tuple" (L.find? (.tuple []))
    let js ← shapeIdxs shs ds ⟨[], .reaction x.name⟩ (L.effectsOf e) (L.ownsOf e)
    let dflt ← need "a pending entry without a default term" (defaultT L (pendingEntry shs))
    let (S, n') := reactSlots dE dP dk dflt js (slotsOf d dt nl 1 lt) n
    let (rest, n'', c2) ← encodeReactions shs ds dE dP xs records now ev n'
    pure (S ++ rest, n'', andT c0 (andT c1 c2))

end

section
variable {L : Layout} {M : Model} {e : Ty}

/-- T2 for a reaction's effect slots: the pending slots hold, where occupied, the requests for its effects in list
order at the ids from `n0`, and the id term after them denotes the id after them. -/
theorem reactSlots_rel {P : List AnySite} (hP : SitesUnique P) (name : String) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)} {js : List Nat}
    (hjs : shapeIdxs shs ds ⟨[], .reaction name⟩ (L.effectsOf e) (L.ownsOf e) = .ok js)
    {dE nE dP nP dk nk : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP)) (hdk : L.find? (.tuple []) = some (dk, nk)) (dflt : Term) :
    (S : List Slot) → (sv : List (Bool × List Val)) → (effs : List (EffectV e)) → SlotsDen M S sv →
    Holds2 (EBag L (.dsl .effect [e])) effs sv → (∀ x ∈ effs, x.Reach P) → {n : Term} → {n0 : Nat} →
    n.denote M = .int n0 →
    (reactSlots dE dP dk dflt js S n).2.denote M = .int ((n0 + effs.length : Nat) : Int) ∧
      NewsRel M L shs ds (reactSlots dE dP dk dflt js S n).1 (effs.map (Sender.reaction name, ·)) n0
  | [], [], effs, _, hh, _, n, n0, hn => by
    cases effs with
    | nil => exact ⟨by simpa [reactSlots] using hn, [], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩
    | cons _ _ => exact hh.elim
  | (f, xs) :: S, (b, vs) :: sv, effs, ⟨hf, hx, hS⟩, hh, hr, n, n0, hn => by
    have hl : (Term.denotes M (pendingItems dE dP dk dflt js [] n (xs.headD tt))).length = 2 := by
      simp [pendingItems, Term.denotes]
    cases b with
    | false =>
      have hn' : (Term.share (.add n (.ite f (.int 1) (.int 0)))).denote M = .int n0 := by
        simp [Term.denote_share, Term.denote, hn, hf, Val.toInt, Val.toBool]
      obtain ⟨h1, sv', zs, hS', hw, hh', xs', hp, hq⟩ :=
        reactSlots_rel hP name hshs hjs hE hPE hdk dflt S sv effs hS (by simpa [Holds2, occupied] using hh) hr hn'
      refine ⟨h1, (false, _) :: sv', zs, ⟨hf, rfl, hS'⟩, ?_, by simpa [Holds2, occupied] using hh', xs', hp, hq⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hl, hw⟩
    | true =>
      match effs, hh with
      | x :: effs, ⟨⟨z, hz, hxz⟩, hh⟩ =>
        have hn' : (Term.share (.add n (.ite f (.int 1) (.int 0)))).denote M = .int ((n0 + 1 : Nat) : Int) := by
          simp [Term.denote_share, Term.denote, hn, hf, Val.toInt, Val.toBool]
        obtain ⟨h1, sv', zs, hS', hw, hh', xs', hp, hq⟩ :=
          reactSlots_rel hP name hshs hjs hE hPE hdk dflt S sv effs hS hh (fun y hy => hr y (by simp [hy])) hn'
        rw [hz] at hx
        obtain ⟨t, rfl, ht⟩ : ∃ t, xs = [t] ∧ t.denote M = z := by
          match xs, hx with
          | [t], hx => simp only [Term.denotes, List.cons.injEq, and_true] at hx; exact ⟨t, rfl, hx⟩
        obtain ⟨req, o, rfl, ho, y, hyrel, hpend⟩ := entry_rel (M := M) hP (.reaction name) hshs hjs hE hPE ()
          (keyT := []) ⟨dk, nk, [], hdk, rfl, rfl⟩ (hr x (by simp)) (effT := Term.share t)
          (by rw [Term.denote_share, ht]; exact hxz) n0 dflt
        refine ⟨by show (reactSlots dE dP dk dflt js S _).2.denote M = _; rw [h1]; simp; omega, (true, _) :: sv',
          ((n0 : Nat), y) :: zs, ⟨hf, rfl, hS'⟩, ?_, ⟨⟨_, _, rfl, by simp only [Term.denote_share]; exact hn, ?_⟩, hh'⟩,
          ((Sender.reaction name, .request req), n0) :: xs', ?_, ⟨⟨rfl, req, o, rfl, ho, hpend⟩, hq⟩⟩
        · simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨hl, hw⟩
        · simp only [List.headD_cons, Term.denote_share]
          exact hyrel
        · simp only [List.map_cons, List.zipIdx_cons]
          exact hp.cons _
  | [], _ :: _, _, h, _, _, _, _, _ | _ :: _, [], _, h, _, _, _, _, _ => h.elim

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

/-- T2 for the reactions' requests: wherever the condition holds, the pending slots hold, where occupied, the requests
for the reactions' effects in the step's order at the ids from `n0`, and the id term after them denotes the id after
them. -/
theorem reactions_rel {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    {dE nE dP nP : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (recs : r.den0) (tnow : Int) (ev : e.den0) (hrd : r.isData = true) (hed : e.isData = true)
    {records now evT : Term} (hrec : RelV L r (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hev : RelV L e (Ty.up _ hed ev) (evT.denote M)) :
    (xs : List (ReactionV r e)) → (∀ x ∈ xs, x.Reach P) → {n : Term} → {n0 : Nat} → n.denote M = .int n0 →
    {news : List Slot} → {n' c : Term} → encodeReactions L shs ds dE dP xs records now evT n = .ok (news, n', c) →
    Holds M c →
    n'.denote M = .int ((n0 + (reactionEffects xs ev recs tnow).length : Nat) : Int) ∧
      NewsRel M L shs ds news (reactionEffects xs ev recs tnow) n0
  | [], _, n, n0, hn, news, n', c, henc, _ => by
    simp only [encodeReactions, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, -⟩ := henc
    exact ⟨by simpa using hn, [], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩
  | x :: xs, hreach, n, n0, hn, news, n', c, henc, hc => by
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
    generalize hrs : reactSlots dE dP dk dflt js (slotsOf d dt nl 1 lt) n = p at henc
    obtain ⟨S, nS⟩ := p
    obtain ⟨⟨rest, n'', c2⟩, h10, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc0, hc12⟩ := (holds_andT _ _).1 hc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc12
    have hl := x.react.code_apply h1 hc0 _ _ (react_args x recs tnow ev hrd hed hrec hnow hev h2 (need_ok.1 h3)
      (need_ok.1 h4)) h5 hc1
    obtain rfl : l = lt := Option.some.inj (need_ok.1 h6)
    obtain ⟨sv, hS, -, -, hh⟩ := list_view hl h7
    have hr1 := ReactionV.reach_effectsAt P x (hreach x (by simp)) ev recs tnow
    obtain ⟨hn1, hnews1⟩ := reactSlots_rel hP x.name hshs h9 hE hPE (need_ok.1 h8) dflt _ sv _ hS hh hr1 hn
    rw [hrs] at hn1 hnews1
    obtain ⟨hn2, hnews2⟩ := reactions_rel hP hshs hE hPE recs tnow ev hrd hed hrec hnow hev xs
      (fun y hy => hreach y (by simp [hy])) hn1 h10 hc2
    have hnews2' : NewsRel M L shs ds rest (reactionEffects xs ev recs tnow)
        (n0 + ((x.effectsAt ev recs tnow).map (Sender.reaction x.name, ·)).length) := by
      rw [List.length_map]; exact hnews2
    simp only [reactionEffects, List.flatMap_cons] at hn2 hnews2' ⊢
    refine ⟨?_, newsRel_append hnews1 hnews2'⟩
    rw [hn2]
    congr 2
    rw [List.length_append, List.length_map, Nat.add_assoc]
    rfl

end

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- The reactions' condition is exact: it holds exactly when every reaction's kept source fits and its application to
the event fits. -/
theorem reactions_exact {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {dE dP : Nat}
    (recs : r.den0) (tnow : Int) (ev : e.den0) (hrd : r.isData = true) (hed : e.isData = true)
    {records now evT : Term} (hrec : RelV L r (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hev : RelV L e (Ty.up _ hed ev) (evT.denote M)) :
    (xs : List (ReactionV r e)) → {n : Term} → {news : List Slot} → {n' c : Term} →
    encodeReactions L shs ds dE dP xs records now evT n = .ok (news, n', c) →
    (Holds M c ↔ ∀ x ∈ xs, (x.react.fits L.count).1 ∧ x.react.appFits L.count (.inl (recs, tnow, ()), ev, ()))
  | [], n, news, n', c, henc => by
    simp only [encodeReactions, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, -, rfl⟩ := henc
    simp [holds_tt]
  | x :: xs, n, news, n', c, henc => by
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
    generalize reactSlots dE dP dk dflt js (slotsOf d dt nl 1 lt) n = p at henc
    obtain ⟨S, nS⟩ := p
    obtain ⟨⟨rest, n'', c2⟩, h10, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have e0 := (x.react.code_exact (M := M) h1).1
    have e1 : ∀ hc0 : Holds M c0, (Holds M c1 ↔ x.react.appFits L.count (.inl (recs, tnow, ()), ev, ())) := fun hc0 =>
      x.react.app_exact h1 hc0 (fun t ht => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact ofTerm_notFn (need_ok.1 h3)
        · exact ofTerm_notFn (need_ok.1 h4)) _ _
        (react_args x recs tnow ev hrd hed hrec hnow hev h2 (need_ok.1 h3) (need_ok.1 h4)) h5
    have e2 := reactions_exact recs tnow ev hrd hed hrec hnow hev xs h10
    rw [holds_andT, holds_andT, e0, e2]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨p0, p1, p2⟩
      exact ⟨⟨p0, (e1 (e0.2 p0)).1 p1⟩, p2⟩
    · rintro ⟨⟨p0, p1⟩, p2⟩
      exact ⟨p0, (e1 (e0.2 p0)).2 p1, p2⟩

end

end Tazuna.Smt
