import Tazuna.Semantics.Step
import Tazuna.Semantics.Forall2

/-! What `start` writes. Each request among the started effects goes into the pending requests at the next wire id,
in order, and out as a line; each own command or query is queued, in order (`start_requests`). -/

namespace Tazuna.Ir

namespace Step

variable {v : ServiceV}

/-- The out line of a pending request: its wire id, external, command or query name and input. -/
def Pending.line {e : Ty} (p : Pending e) : OutLine := ⟨p.id, p.external, p.request.name, ⟨p.request.input, p.request.value⟩⟩

/-- An effect with its wire id is the request `p` the step writes for it: a request, to the external that lists it. -/
def Writes (ds : List (String × DeclaredV)) {e : Ty} (x : (Sender × EffectV e) × Nat) (p : Pending e) : Prop :=
  ∃ r o, x.1.2 = .request r ∧ r.ownerIn ds = some o ∧ p = ⟨x.2, x.1.1, o, r⟩

/-- The step in progress `a` with the requests `ps` written and sent and the next id `n`. -/
def Acc.wrote (a : Acc v) (ps : List (Pending v.event)) (n : Nat) : Acc v :=
  { a with state := { a.state with pending := a.state.pending ++ ps, nextId := n }, out := a.out ++ ps.map Pending.line }

/-- The step in progress `a` with the own commands and queries `os` queued after the waiting ones. -/
def Acc.queued (a : Acc v) (os : List (OwnEffectV v.event)) : Acc v := { a with own := a.own ++ os }

/-- The requests among effects, in order. -/
abbrev reqsOf {e : Ty} (effs : List (Sender × EffectV e)) : List (Sender × EffectV e) := effs.filter (·.2.isRequest)

/-- The own commands and queries among effects, in order: what they queue. -/
abbrev queuedOf {e : Ty} (effs : List (Sender × EffectV e)) : List (OwnEffectV e) :=
  effs.filterMap (·.2.own?)

theorem queuedOf_effect {e : Ty} : (effs : List (Sender × EffectV e)) →
    (queuedOf effs).map OwnEffectV.effect = (effs.filter (!·.2.isRequest)).map (·.2)
  | [] => rfl
  | (_, .request _) :: effs => by simpa [queuedOf, EffectV.own?, EffectV.isRequest] using queuedOf_effect effs
  | (_, .command ..) :: effs => by
    simp only [queuedOf, List.filterMap_cons, EffectV.own?, List.map_cons, OwnEffectV.effect, List.filter_cons,
      EffectV.isRequest, Bool.not_false, ↓reduceIte]
    exact congrArg _ (queuedOf_effect effs)
  | (_, .query ..) :: effs => by
    simp only [queuedOf, List.filterMap_cons, EffectV.own?, List.map_cons, OwnEffectV.effect, List.filter_cons,
      EffectV.isRequest, Bool.not_false, ↓reduceIte]
    exact congrArg _ (queuedOf_effect effs)

theorem length_queuedOf {e : Ty} (effs : List (Sender × EffectV e)) :
    (queuedOf effs).length = (effs.filter (!·.2.isRequest)).length := by
  simpa using congrArg List.length (queuedOf_effect effs)

theorem queuedOf_eq_nil {e : Ty} {effs : List (Sender × EffectV e)} (h : ∀ x ∈ effs, x.2.isRequest = true) :
    queuedOf effs = [] := by
  have hl := length_queuedOf effs
  rw [List.filter_eq_nil_iff.2 fun x hx => by simp [h x hx], List.length_nil] at hl
  exact List.eq_nil_of_length_eq_zero hl

/-- Starting effects writes the requests, which externals list, into the pending table at the next ids and sends
them, and queues the own commands and queries, each in order. -/
theorem start_requests (a : Acc v) : (effs : List (Sender × EffectV v.event)) → (ps : List (Pending v.event)) →
    Tazuna.Ir.Forall2 (Writes v.declared) ((reqsOf effs).zipIdx a.state.nextId) ps →
    start a effs = .ok ((a.wrote ps (a.state.nextId + (reqsOf effs).length)).queued (queuedOf effs))
  | [], [], _ => by
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [start, pure, Except.pure, Acc.wrote, Acc.queued]
  | (snd, .request r) :: effs, p :: ps, ⟨⟨r', o, he, ho, hp⟩, hs⟩ => by
    simp only at he hp
    cases he
    subst hp
    have h1 : start a ((snd, .request r) :: effs) =
        start (a.wrote [⟨a.state.nextId, snd, o, r⟩] (a.state.nextId + 1)) effs := by
      simp only [start, List.foldlM_cons, ho, bind, Except.bind]; rfl
    rw [h1, start_requests _ effs ps hs]
    have hl : (reqsOf ((snd, EffectV.request r) :: effs)).length = (reqsOf effs).length + 1 := by
      simp [reqsOf, EffectV.isRequest]
    have hq : queuedOf ((snd, EffectV.request r) :: effs) = queuedOf effs := by simp [queuedOf, EffectV.own?]
    rw [hl, hq]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp only [Acc.wrote, Acc.queued, List.append_assoc, List.cons_append, List.nil_append, List.map_cons,
      Pending.line, Except.ok.injEq]
    congr 2
    omega
  | (snd, .command n c i j caller value f) :: effs, ps, hs => by
    have h1 : start a ((snd, .command n c i j caller value f) :: effs) =
        start (a.queued [.command n c i j caller value f]) effs := rfl
    have hr : reqsOf ((snd, EffectV.command n c i j caller value f) :: effs) = reqsOf effs := rfl
    have hq : queuedOf ((snd, EffectV.command n c i j caller value f) :: effs) =
        .command n c i j caller value f :: queuedOf effs := rfl
    rw [hr] at hs
    rw [h1, start_requests (a.queued _) effs ps hs, hr, hq]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [Acc.wrote, Acc.queued]
  | (snd, .query n c i j caller value f) :: effs, ps, hs => by
    have h1 : start a ((snd, .query n c i j caller value f) :: effs) =
        start (a.queued [.query n c i j caller value f]) effs := rfl
    have hr : reqsOf ((snd, EffectV.query n c i j caller value f) :: effs) = reqsOf effs := rfl
    have hq : queuedOf ((snd, EffectV.query n c i j caller value f) :: effs) =
        .query n c i j caller value f :: queuedOf effs := rfl
    rw [hr] at hs
    rw [h1, start_requests (a.queued _) effs ps hs, hr, hq]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [Acc.wrote, Acc.queued]
  | [], _ :: _, h => h.elim
  | (_, .request _) :: _, [], h => h.elim

end Step

end Tazuna.Ir
