import Tazuna.Smt.PairCompare
import Tazuna.Smt.Cti
import Tazuna.Smt.InternalDispatch
import Tazuna.Smt.Names
import Tazuna.Semantics.PairCommute
import Tazuna.Smt.DecodeRel

/-! The question T5 asks of a listed pair of own kinds (`Step.PairCommutes`, `Layout.ownPairs`): from a symbolic state,
the first effect runs then the second (order A), and the second runs at the next counter then the first at the
current one (the canonical order, `Step.canonPair`), each internal step encoded for its kind. The two orders commute
when the first does not fault, or when the second faults first and still faults after it, or when both orders fault,
or when both end with records and instance tables Gleam's `==` finds equal and each effect does the same in both
orders: it applies the same events, sends the same requests at the same ids counted from where its step starts, and
queues the same own commands and queries, each in the same slots. In the canonical order each effect gets the counter
and the wire ids it gets in order A, so no renaming is searched for (`pair_sound`). Comparing slot by slot is stricter
than the semantics, which reads every collection as a multiset: a pair whose steps write the same things into other
slots is reported as not commuting, never the other way round.

The pairs of own kinds T5 asks about. `Step.PairCommutes` is a question about two waiting own effects in an order:
the first runs first, and the other order is the canonical one. A pair whose second effect faults alone but not after
the first is a disabling the other order shows, so both orders of two kinds are asked, and a kind with itself, since
two effects of one kind are two effects. The pairs are the ordered pairs of the own kinds' places among the variants of
the effect datatype (`Layout.ownPairs`), and every two own effects a model codes fall under one
(`ownPairs_complete`, T5b): the kind coverage theorems give every own effect a step starts a variant, so no pair of
waiting effects escapes the questions. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- An own kind's place among the own kinds of the event type `e`. -/
abbrev OwnPlace (L : Layout) (e : Ty) := Fin (L.ownsOf e).length

/-- The variant of the effect datatype an own kind has: the own kinds come after the request kinds. -/
def Layout.ownCtor (L : Layout) (e : Ty) (k : OwnPlace L e) : Nat := (L.effectsOf e).length + k

/-- The ordered pairs of own kinds of the event type `e`, self-pairs included. -/
def Layout.ownPairs (L : Layout) (e : Ty) : List (OwnPlace L e × OwnPlace L e) :=
  (List.finRange _).flatMap fun i => (List.finRange _).map fun j => (i, j)

theorem mem_ownPairs {L : Layout} {e : Ty} (p : OwnPlace L e × OwnPlace L e) : p ∈ L.ownPairs e :=
  List.mem_flatMap.2 ⟨p.1, List.mem_finRange _, List.mem_map.2 ⟨p.2, List.mem_finRange _, rfl⟩⟩

/-- The fields of the own kind `k`'s variant of the effect at `z` are well formed, as an input's are (`SymInput.wf`):
its caller, its input and its `on_answer`'s captured values, so a model's effect of the kind decodes. -/
def ownWf (L : Layout) (e : Ty) (dE : Nat) (k : OwnPlace L e) (z : Term) : Option Term :=
  ((L.ownsOf e)[k].fields.zipIdx.mapM fun (t, j) => wfT L t (.sel dE (L.ownCtor e k) j z)).map allT

/-- The type of an own kind's `on_answer`: it takes the command's result or the query's output. -/
def OwnKey.answerFn (e : Ty) : OwnKey → Ty
  | .command _ _ _ _ rj _ => Ty.fn [Ty.result Ty.nil rj] (.list e)
  | .query _ _ _ _ o _ => Ty.fn [o] (.list e)

/-- Whether the program writes the own kind `k`'s `on_answer` at a site of `P`, so its effects decode
(`decodeOwn`). A kind the layout lists but the program never builds has no effect that reaches `P`
(`ownFound_of_reach`). -/
def ownFound (P : List AnySite) (L : Layout) (e : Ty) (k : OwnPlace L e) : Bool :=
  (siteFor P ((L.ownsOf e)[k].answerFn e) (L.ownsOf e)[k].answer).isSome

/-- An own effect's code is the variant of an own kind. -/
theorem own_variant {L : Layout} {e : Ty} {x : OwnEffectV e} {z : Val} (hx : EffRel L x.effect z) :
    ∃ d n, ∃ k : OwnPlace L e, ∃ vals, L.find? (.dsl .effect [e]) = some (d, n) ∧ z = .ctor d (L.ownCtor e k) vals := by
  obtain ⟨d, n, hd, ⟨_, _, _, -, -, hh⟩ | ⟨k, key, vals, hk, rfl, -⟩⟩ := hx
  · cases x <;> exact hh.elim
  · exact ⟨d, n, ⟨k, (List.getElem?_eq_some_iff.1 hk).1⟩, vals, hd, rfl⟩

/-- T5b: any two own effects a model codes are effects of a listed pair of own kinds, in their order. -/
theorem ownPairs_complete {L : Layout} {e : Ty} {x1 x2 : OwnEffectV e} {z1 z2 : Val} (h1 : EffRel L x1.effect z1)
    (h2 : EffRel L x2.effect z2) :
    ∃ p ∈ L.ownPairs e, ∃ d n vals1 vals2, L.find? (.dsl .effect [e]) = some (d, n) ∧
      z1 = .ctor d (L.ownCtor e p.1) vals1 ∧ z2 = .ctor d (L.ownCtor e p.2) vals2 := by
  obtain ⟨d, n, k1, vals1, hd, rfl⟩ := own_variant h1
  obtain ⟨d', n', k2, vals2, hd', rfl⟩ := own_variant h2
  rw [hd] at hd'
  cases hd'
  exact ⟨(k1, k2), mem_ownPairs _, d, n, vals1, vals2, hd, rfl, rfl⟩

section
variable (L : Layout)

/-- Each machine's instance tables compared by Gleam's `==`. -/
def tablesEqT {r e : Ty} : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → PerMachine (fun _ => Term) ms →
    Except Refusal Term
  | [], .nil, .nil => .ok tt
  | m :: ms, .cons x xs, .cons y ys => do
    let f ← eqFn L m.table
    pure (.and (f x y) (← tablesEqT ms xs ys))

/-- A pair question's terms: whether the two orders do not commute, the condition that every step reached fits, and
the codes' condition. -/
structure PairOut where
  viol : Term
  cond : Term
  codes : Term

variable (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))

/-- The pair of own kinds `k1`, `k2` (places among the own kinds) from the symbolic state `S`, with the effects
`e1` and `e2`, in order A and in the canonical order. -/
def encodePair (S : SymState v) (e1 e2 : Term) (k1 k2 : OwnPlace L v.event) : Except Refusal PairOut := do
  let (apply, ca) ← v.apply.code L
  let nR := (L.effectsOf v.event).length
  let key1 := (L.ownsOf v.event)[k1]
  let key2 := (L.ownsOf v.event)[k2]
  let step (records fresh n q eff : Term) (xs : PerMachine (fun _ => Term) v.machines) (j : Nat) (key : OwnKey) :=
    encodeOwnKind L T P v (shapes v) senv nR apply records S.now fresh n q eff xs j key
  let ⟨⟨_, a1⟩, c1, x1⟩ ← step S.records S.fresh S.nextId (.int 0) e1 S.machines k1 key1
  let ⟨⟨_, a2⟩, c2, x2⟩ ← step a1.done.records a1.fresh a1.done.nextId a1.done.queued e2 a1.done.tables k2 key2
  let ⟨⟨_, b1⟩, c3, x3⟩ ← step S.records (.add S.fresh (.int 1)) S.nextId (.int 0) e2 S.machines k2 key2
  let ⟨⟨_, b2⟩, c4, x4⟩ ← step b1.done.records S.fresh b1.done.nextId b1.done.queued e1 b1.done.tables k1 key1
  let recEq ← eqFn L v.records
  let tabEq ← tablesEqT L v.machines a2.done.tables b2.done.tables
  let same := allT [recEq a2.done.records b2.done.records, tabEq, slotsEqT a1.done.events b2.done.events,
    slotsEqT a2.done.events b1.done.events, newsEqT S.nextId b1.done.nextId a1.done.news b2.done.news,
    newsEqT a1.done.nextId S.nextId a2.done.news b1.done.news, ownsEqT a1.done.owns b2.done.owns,
    ownsEqT a2.done.owns b1.done.owns]
  let viol := Term.and (.not a1.fault) (.or (.and b1.fault (.not a2.fault))
    (.and (.not b1.fault) (.and (.not (.and a2.fault b2.fault)) (.not (.and (.not a2.fault) (.and (.not b2.fault) same))))))
  pure ⟨viol, allT [c1, c3, .ite a1.fault tt c2, .ite b1.fault tt c4], allT [ca, x1, x2, x3, x4]⟩

/-- The types of a pair question's variables: the state's, then the two effects. -/
def pairTys : List Ty := stateTys v (shapes v) ++ [.dsl .effect [v.event], .dsl .effect [v.event]]

/-- The place of the first effect's variable, after the state's. -/
def pairVar : Nat := stateWidth v

/-- A pair's two questions, over a well-formed state whose names are below its counter and pending ids below its next
id, and well-formed effects of the two kinds: the bound question, whether the codes' condition or a step reached leaves the
slots; and the target question, whether the two orders do not commute where everything fits. A pair with a kind the
program never builds (`ownFound`) asserts false: no effect of it exists, so both questions are unsat and no model of
an effect that does not decode is asked for. -/
def pairQuestions (k1 k2 : OwnPlace L v.event) : Except Refusal (TypedScript × TypedScript) := do
  let S : SymState v := SymState.vars 0
  let n := pairVar v
  let o ← encodePair L T P v senv S (.var n) (.var (n + 1)) k1 k2
  let wf ← need (.layout (.type v.records)) (S.wf L (shapes v))
  let below ← pendingBelowT L (shapes v) S.pending S.nextId
  let names ← need (.layout (.type v.records)) (namesStateT L S)
  let tests := [Term.is senv.dE (L.ownCtor v.event k1) (.var n), .is senv.dE (L.ownCtor v.event k2) (.var (n + 1))]
  let w1 ← need (lacksDatas (L.ownsOf v.event)[k1].fields) (ownWf L v.event senv.dE k1 (.var n))
  let w2 ← need (lacksDatas (L.ownsOf v.event)[k2].fields) (ownWf L v.event senv.dE k2 (.var (n + 1)))
  let vars ← (pairTys v).mapM fun ty => need (lacks ty) (L.srt? ty)
  let dts ← need (.layout (.type v.records)) L.datatypes?
  let found := if ownFound P L v.event k1 && ownFound P L v.event k2 then [] else [Term.bool false]
  let script (asserts : List Term) : TypedScript :=
    ⟨dts, pairTys v, vars, [wf, below, names] ++ tests ++ [w1, w2] ++ found, asserts⟩
  pure (script [.or (.not o.codes) (.not o.cond)], script [o.codes, o.cond, o.viol])

/-- The data value of type `t` an SMT value codes. -/
def readData (t : Ty) (z : Val) : Option t.den0 :=
  if h : t.isData = true then (decodeV L t z).map (Ty.down t h) else none

/-- The own effect of the `k`-th own kind that a model's value codes: the kind's command or query with the input its
fields code, answered by the program's site the kind names with the captured values its last field codes. -/
def decodeOwn (k : OwnPlace L v.event) (z : Val) : Option (OwnEffectV v.event) := do
  let .ctor _ i vals := z | none
  if i ≠ L.ownCtor v.event k then none
  match (L.ownsOf v.event)[k], vals with
  | .command _ name c j rj a, [vi, va] =>
    let ⟨Γ, site⟩ ← siteFor P (Ty.fn [Ty.result Ty.nil rj] (.list v.event)) a
    pure (.command name c j rj (← readData L j vi) (site.fn (← readData L (.tuple Γ) va)))
  | .query _ name c j o a, [vi, va] =>
    let ⟨Γ, site⟩ ← siteFor P (Ty.fn [o] (.list v.event)) a
    pure (.query name c j o (← readData L j vi) (site.fn (← readData L (.tuple Γ) va)))
  | _, _ => none

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- The fields of an own kind's variant that codes an own effect code data of the kind's field types. -/
theorem ownFields_rel {e : Ty} {key : OwnKey} {x : OwnEffectV e} {vals : List Val} (hh : key.Holds L x.effect vals) :
    Forall2 (fun t z => ∃ y, RelD L t y z) key.fields vals := by
  cases key with
  | command e' name c i j a =>
    cases x with
    | query => exact hh.elim
    | command name' c' i' j' value onAnswer =>
      obtain ⟨-, rfl, rfl, -, -, hΓ, vi, va, rfl, hi, hcap⟩ := hh
      have hv : ∃ y, RelD L (.tuple onAnswer.Γ) y va := ⟨_, hcap⟩
      rw [hΓ] at hv
      exact ⟨⟨_, hi⟩, hv, trivial⟩
  | query e' name c i o a =>
    cases x with
    | command => exact hh.elim
    | query name' c' i' o' value onAnswer =>
      obtain ⟨-, rfl, rfl, -, -, hΓ, vi, va, rfl, hi, hcap⟩ := hh
      have hv : ∃ y, RelD L (.tuple onAnswer.Γ) y va := ⟨_, hcap⟩
      rw [hΓ] at hv
      exact ⟨⟨_, hi⟩, hv, trivial⟩

/-- A model's value of an own kind's variant that codes an own effect has well-formed fields (`ownWf`), so a pair
question's context, which asserts them, holds at every pair of effects a step can queue. The fields are comparable
in a sorted layout, which is what decoding a table's keys needs. -/
theorem ownWf_holds (hL : SortedLayout L) {d n : Nat} (hd : L.find? (.dsl .effect [v.event]) = some (d, n)) {k : OwnPlace L v.event}
    {x : OwnEffectV v.event} {i : Nat} (hx : RelV L (.dsl .effect [v.event]) x.effect (M.vars i))
    (ht : Holds M (.is d (L.ownCtor v.event k) (.var i))) {c : Term}
    (hw : ownWf L v.event d k (.var i) = some c) : Holds M c := by
  obtain ⟨d', n', hd', hr⟩ := hx
  rw [hd] at hd'
  cases hd'
  rcases hr with ⟨k0, key, vals, hk0, hz, -⟩ | ⟨k0, key, vals, hk0, hz, hh⟩
  · have hlt : k0 < (L.effectsOf v.event).length := (List.getElem?_eq_some_iff.1 hk0).1
    simp [Holds, Term.denote, hz, Val.toBool, Layout.ownCtor] at ht
    omega
  · have hk : k0 = k.val := by
      simp [Holds, Term.denote, hz, Val.toBool, Layout.ownCtor] at ht
      omega
    subst hk
    have hkey : (L.ownsOf v.event)[k] = key := by
      rw [List.getElem?_eq_getElem k.isLt] at hk0; exact Option.some.inj hk0
    have hcmp := hL.ownsComparable (hkey ▸ List.getElem_mem k.isLt)
    unfold ownWf at hw
    rw [hkey] at hw
    obtain ⟨cs, hcs, rfl⟩ := map_some.1 hw
    rw [holds_allT]
    intro c' hc'
    obtain ⟨⟨t, j⟩, hmem, hcj⟩ := forall2_mem_left (mapM_forall2 (E := fun c q => wfT L q.1
      (.sel d (L.ownCtor v.event k) q.2 (.var i)) = some c) (fun _ _ h => h) _ _ hcs) c' hc'
    have hj : key.fields[j]? = some t := List.mem_zipIdx_iff_getElem?.1 hmem
    obtain ⟨z, hzj, y, hy⟩ := forall2_getElem? (ownFields_rel hh) hj
    have htc : t.comparable = true := hcmp t (List.mem_of_getElem? hj)
    have hden : (Term.sel d (L.ownCtor v.event k) j (.var i)).denote M = z := by
      simp [Term.denote, hz, hzj, Layout.ownCtor]
    obtain ⟨y', hy', -⟩ := decode_of_relV htc (relD_up t (Ty.isData_of_comparable t htc) y z hy)
    exact wfT_of_decodeV hcj (by rw [hden]; exact hy')

/-- An effect that reaches `P` and is coded at an own kind's variant has a kind the program builds. -/
theorem ownFound_of_reach {P : List AnySite} {d n : Nat} (hd : L.find? (.dsl .effect [v.event]) = some (d, n))
    {k : OwnPlace L v.event} {x : OwnEffectV v.event} {i : Nat}
    (hx : RelV L (.dsl .effect [v.event]) x.effect (M.vars i)) (ht : Holds M (.is d (L.ownCtor v.event k) (.var i)))
    (hr : x.effect.Reach P) : ownFound P L v.event k = true := by
  obtain ⟨d', n', hd', hrel⟩ := hx
  rw [hd] at hd'
  cases hd'
  rcases hrel with ⟨k0, key, vals, hk0, hz, -⟩ | ⟨k0, key, vals, hk0, hz, hh⟩
  · have hlt : k0 < (L.effectsOf v.event).length := (List.getElem?_eq_some_iff.1 hk0).1
    simp [Holds, Term.denote, hz, Val.toBool, Layout.ownCtor] at ht
    omega
  · have hk : k0 = k.val := by
      simp [Holds, Term.denote, hz, Val.toBool, Layout.ownCtor] at ht
      omega
    subst hk
    have hkey : (L.ownsOf v.event)[k] = key := by
      rw [List.getElem?_eq_getElem k.isLt] at hk0; exact Option.some.inj hk0
    unfold ownFound
    rw [hkey]
    cases key <;> cases hx : x.effect <;> rw [hx] at hh hr <;> simp only [OwnKey.Holds] at hh
    · obtain ⟨-, -, -, rfl, hs, hΓ, -⟩ := hh
      exact Option.ne_none_iff_isSome.1 (siteFor_reach hr hs hΓ)
    · obtain ⟨-, -, -, rfl, hs, hΓ, -⟩ := hh
      exact Option.ne_none_iff_isSome.1 (siteFor_reach hr hs hΓ)

/-- Two steps in progress that extend `a0` by alike requests at the same ids from `a0`'s next id on (with their out
lines), by related own effects and events, and whose records and instances relate, are the same with every name kept. -/
theorem same_of_parts {a0 A C : Step.Acc v} (h0 : Step.Acc.Rel ⟨PBij.refl, PBij.refl⟩ a0 a0)
    (hr : Ty.rel0 PBij.refl v.records A.state.records C.state.records)
    (hm : Step.Machines.Rel PBij.refl A.state.machines C.state.machines)
    {PA PC : List (Step.Pending v.event)} (hpA : A.state.pending = a0.state.pending ++ PA)
    (hpC : C.state.pending = a0.state.pending ++ PC)
    (hP : Multi (fun p q => p.id = q.id ∧ PendingAlike PBij.refl p q) PA PC)
    (hPn : ∀ p ∈ PA, a0.state.nextId ≤ p.id ∧ p.id < A.state.nextId)
    (hnA : A.state.now = a0.state.now) (hnC : C.state.now = a0.state.now)
    (hi : A.state.nextId = C.state.nextId) (hiA : a0.state.nextId ≤ A.state.nextId)
    (hoA : A.out = a0.out ++ PA.map Step.Pending.line) (hoC : C.out = a0.out ++ PC.map Step.Pending.line)
    {OA OC : List (OwnEffectV v.event)} (hwA : A.own = a0.own ++ OA) (hwC : C.own = a0.own ++ OC)
    (hO : Multi (OwnEffectV.Rel PBij.refl) OA OC)
    {EA EC : List v.event.den0} (heA : A.events = a0.events ++ EA) (heC : C.events = a0.events ++ EC)
    (he : Multi (Ty.rel0 PBij.refl v.event) EA EC) (hf : A.state.fresh = C.state.fresh) {f0 : Nat} :
    Step.Same f0 a0.state.nextId A C := by
  obtain ⟨⟨-, -, hp, -, hb, -⟩, hev, hout, ho, -, hown⟩ := h0
  have hPC : ∀ q ∈ PC, a0.state.nextId ≤ q.id ∧ q.id < A.state.nextId := fun q hq => by
    obtain ⟨p, hp', hpq, -⟩ := hP.flip.mem_left hq
    rw [← hpq]; exact hPn p hp'
  have hnew : Multi (Step.Pending.Rel ⟨PBij.refl, PBij.refl⟩) PA PC := hP.imp_mem fun _ _ _ _ h => ⟨h.1, h.2⟩
  have hbelow : ∀ {xs : List (Step.Pending v.event)}, (∀ q ∈ xs, q.id < A.state.nextId) →
      ∀ q ∈ a0.state.pending ++ xs, q.id < A.state.nextId := fun hx q hq =>
    (List.mem_append.1 hq).elim (fun h => Nat.lt_of_lt_of_le (hb q h) hiA) (hx q)
  have hobelow : ∀ {xs : List (Step.Pending v.event)}, (∀ q ∈ xs, q.id < A.state.nextId) →
      ∀ o ∈ a0.out ++ xs.map Step.Pending.line, o.id < A.state.nextId := fun hx o hq =>
    (List.mem_append.1 hq).elim (fun h => Nat.lt_of_lt_of_le (ho o h) hiA)
      fun h => by obtain ⟨q, hq', rfl⟩ := List.mem_map.1 h; exact hx q hq'
  refine .base ⟨⟨PBij.refl, PBij.refl⟩, ⟨⟨hr, hm, ?_, hnA.trans hnC.symm, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hf, hi, hiA,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · rw [hpA, hpC]; exact hp.append hnew
  · rw [hpA]; exact hbelow fun q hq => (hPn q hq).2
  · rw [hpC, ← hi]; exact hbelow fun q hq => (hPC q hq).2
  · rw [heA, heC]; exact hev.append he
  · rw [hoA, hoC]; exact hout.append (hnew.map fun _ _ h => Step.Pending.rel_line h)
  · rw [hoA]; exact hobelow fun q hq => (hPn q hq).2
  · rw [hoC, ← hi]; exact hobelow fun q hq => (hPC q hq).2
  · rw [hwA, hwC]; exact hown.append hO

/-- Requests alike, each at the id `σ` gives the other's, are alike at the same ids once the second side's ids are
renamed by `σ`. -/
theorem multi_rewire {e : Ty} {σ : Nat → Nat} {xs ys : List (Step.Pending e)}
    (h : Multi (fun p q => p.id = σ q.id ∧ PendingAlike PBij.refl p q) xs ys) :
    Multi (fun p q => p.id = q.id ∧ PendingAlike PBij.refl p q) xs (ys.map fun q => { q with id := σ q.id }) := by
  simpa using h.map (r' := fun p q => p.id = q.id ∧ PendingAlike PBij.refl p q) (f := id)
    (g := fun q : Step.Pending e => { q with id := σ q.id }) fun _ _ h => h

/-- The variant test of an own kind's place and an effect's code give the kind's facts of the effect. -/
theorem own_key {x : OwnEffectV v.event} {senv : StepEnv L (shapes v)} {z : Val}
    (hx : RelV L (.dsl .effect [v.event]) x.effect z) {k : OwnPlace L v.event} {t : Term}
    (ht : Holds M (.is senv.dE (L.ownCtor v.event k) t)) (hz : t.denote M = z) :
    ∃ vals, z = .ctor senv.dE (L.ownCtor v.event k) vals ∧ (L.ownsOf v.event)[k].Holds L x.effect vals := by
  have hx' : EffRel L x.effect z := hx
  obtain ⟨d, nn, hd, hx'⟩ := hx'
  cases (Prod.mk.inj (Option.some.inj (senv.hE.symm.trans hd))).1
  rcases hx' with ⟨_, _, _, -, -, hh⟩ | ⟨k', key', vals, hk', rfl, hh⟩
  · cases x <;> exact hh.elim
  · simp only [Holds, Term.denote, hz, Val.toBool, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht
    simp only [Layout.ownCtor] at ht ⊢
    have hk : k' = k := by omega
    subst hk
    rw [List.getElem?_eq_getElem k.isLt] at hk'
    cases hk'
    exact ⟨vals, rfl, hh⟩

/-- Instance tables compared equal hold the same instances, read as multisets. -/
theorem machines_of_eq : (ms : List (MachineV v.records v.event)) →
    (∀ m ∈ ms, m.key.comparable = true ∧ m.state.comparable = true) →
    {xs ys : PerMachine (fun _ => Term) ms} → {sa sb : Step.Machines ms} → MachinesRel M L T ms xs sa →
    MachinesRel M L T ms ys sb → {c : Term} → tablesEqT L ms xs ys = .ok c → Holds M c →
    Step.Machines.Rel PBij.refl sa sb
  | [], _, .nil, .nil, .nil, .nil, _, _, _, _, _ => trivial
  | m :: ms, hc, .cons x xs, .cons y ys, .cons ia sa, .cons ib sb, ⟨⟨ta, hta, hia⟩, ha⟩, ⟨⟨tb, htb, hib⟩, hb⟩, c, h,
      hh => by
    subst hia hib
    obtain ⟨f, hf, h⟩ := bind_ok.1 h
    obtain ⟨c', hc', h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_and] at hh
    have hm := hc m (List.mem_cons_self ..)
    have htc : m.table.comparable = true := by
      simp only [MachineV.table, Ty.comparable, Bool.and_eq_true]
      exact ⟨hm.1, instEntry_comparable hm.2⟩
    exact ⟨insts_of_table (rel0_of_eqFn m.table_data htc hta htb hf hh.1),
      machines_of_eq ms (fun m' hm' => hc m' (List.mem_cons_of_mem _ hm')) ha hb hc' hh.2⟩

theorem fault_true {t : Term} {o : Option Fault} (h : t.denote M = .bool o.isSome) : Holds M t ↔ o.isSome := by
  simp [Holds, h, Val.toBool]

/-- A pair question's terms: where the codes' condition and the condition hold and the two orders are not reported as
not commuting, the two effects commute from every step in progress whose state the symbolic state denotes, whose
pending requests and own queue hold kept functions of `P`, and which relates to itself under every renaming keeping
its counters (`Step.PairCommutes`). -/
theorem pair_commutes {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v))
    {S : SymState v} {a0 : Step.Acc v} (hR : StateRel M L T (shapes v) S a0.state) (hinv : Step.Inv P a0.state)
    (hqk : Step.QueueOk P a0) (hsa : Below Step.Acc.Self a0.state.fresh a0) {t1 t2 : Term} {x1 x2 : OwnEffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (t1.denote M)) (hx2 : RelV L (.dsl .effect [v.event]) x2.effect (t2.denote M))
    (hreach1 : x1.effect.Reach P) (hreach2 : x2.effect.Reach P)
    {k1 k2 : OwnPlace L v.event} (ht1 : Holds M (.is senv.dE (L.ownCtor v.event k1) t1))
    (ht2 : Holds M (.is senv.dE (L.ownCtor v.event k2) t2))
    {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o)
    (hcodes : Holds M o.codes) (hcond : Holds M o.cond) (hviol : ¬ Holds M o.viol) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko1, a1⟩, c1, y1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko2, a2⟩, c2, y2⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko3, b1⟩, c3, y3⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko4, b2⟩, c4, y4⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨recEq, hrecEq, henc⟩ := bind_ok.1 henc
  obtain ⟨tabEq, htabEq, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcodes hcond
  obtain ⟨hca, hy1, hy2, hy3, hy4⟩ := hcodes
  obtain ⟨hc1, hc3, hc2, hc4⟩ := hcond
  have hshs : ∀ sh ∈ shapes v, sh.InSites P := fun _ => shapes_inSites chk.reach
  obtain ⟨vals1, he1, hk1⟩ := own_key hx1 ht1 rfl
  obtain ⟨vals2, he2, hk2⟩ := own_key hx2 ht2 rfl
  have hq0 : (Term.int 0).denote M = .int ((0 : Nat) : Int) := rfl
  have eA1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0
    hR.machines x1 hreach1 he1 hk1 h1 hy1
  obtain ⟨hfA1, hA1⟩ := eA1.2 hc1
  have hn0 : a0.state.nextId = a0.state.nextId := rfl
  generalize hf : a0.state.fresh = f at hsa
  intro b hb
  -- The first effect runs to its end in order A.
  revert hA1
  cases hko1 : ko1.fault? M with
  | some g => intro hA1; rw [hA1] at hb; cases hb
  | none =>
  intro hA1
  rw [hb] at hA1
  have hfa1 : ¬ Holds M a1.fault := by rw [fault_true hfA1, hko1]; simp
  have hc2' : Holds M c2 := by
    rw [holds_ite] at hc2
    simpa [show (a1.fault.denote M).toBool = false by simpa [Holds] using hfa1] using hc2
  obtain ⟨hbr, hbm, hbf, hbn, hbnow, _, -, hbq, -⟩ := hA1.ends
  have hqb := Step.runOwn_queue T chk.reach a0 hinv hqk x1 hb
  have hinvb := Step.runOwn_inv T chk.reach a0 hinv x1 hb
  have eA2 := ownKind_encode chk hshs (shapesHold_shapes v) b happ hca senv hbr (hR.now.trans (by rw [hbnow])) hbf hbn
    hbq hbm x2 hreach2 he2 hk2 h2 hy2
  obtain ⟨hfA2, hA2⟩ := eA2.2 hc2'
  have hfr1 : (Term.add S.fresh (.int 1)).denote M = .int (Int.ofNat (a0.withFresh (a0.state.fresh + 1)).state.fresh) := by
    simp only [Term.denote, hR.fresh, Val.toInt, Step.Acc.withFresh]; push_cast; rfl
  have eC1 := ownKind_encode chk hshs (shapesHold_shapes v) (a0.withFresh (a0.state.fresh + 1)) happ hca senv hR.records
    hR.now hfr1 hR.nextId hq0 hR.machines x2 hreach2 he2 hk2 h3 hy3
  obtain ⟨hfC1, hC1⟩ := eC1.2 hc3
  simp only [Step.Acc.withFresh, hf] at hC1 ⊢
  refine ⟨fun c hc => ?_, fun g hg => ?_⟩
  · revert hC1
    cases hko3 : ko3.fault? M with
    | some g => intro hC1; rw [hC1] at hc; cases hc
    | none =>
    intro hC1
    rw [hc] at hC1
    have hfb1 : ¬ Holds M b1.fault := by rw [fault_true hfC1, hko3]; simp
    have hc4' : Holds M c4 := by
      rw [holds_ite] at hc4
      simpa [show (b1.fault.denote M).toBool = false by simpa [Holds] using hfb1] using hc4
    obtain ⟨hcr, hcm, -, hcn, hcnow, _, -, hcq, -⟩ := hC1.ends
    have hqc := Step.runOwn_queue T chk.reach { a0 with state := { a0.state with fresh := f + 1 } }
      (hinv.congr rfl rfl) hqk x2 hc
    have hinvc : Step.Inv P (c.withFresh f).state :=
      (Step.runOwn_inv T chk.reach { a0 with state := { a0.state with fresh := f + 1 } } (hinv.congr rfl rfl) x2
        hc).congr rfl rfl
    have hff : S.fresh.denote M = .int (Int.ofNat (c.withFresh f).state.fresh) := by
      simp only [Step.Acc.withFresh]; rw [hR.fresh, hf]
    have eC2 := ownKind_encode chk hshs (shapesHold_shapes v) (c.withFresh f) happ hca senv hcr
      (hR.now.trans (by rw [← hcnow]; rfl)) hff hcn hcq hcm x1 hreach1 he1 hk1 h4 hy4
    obtain ⟨hfC2, hC2⟩ := eC2.2 hc4'
    simp only [Step.canonPair, Step.Acc.withFresh, hf, hc, bind, Except.bind] at hC2 ⊢
    simp only [holds_and, holds_or, holds_not, not_and, not_or, Classical.not_not] at hviol
    have hv := (hviol hfa1).2 hfb1
    have key : (Holds M a2.fault ∧ Holds M b2.fault) ∨ (¬ Holds M a2.fault ∧ ¬ Holds M b2.fault ∧
        Holds M (allT [recEq a2.done.records b2.done.records, tabEq, slotsEqT a1.done.events b2.done.events,
          slotsEqT a2.done.events b1.done.events, newsEqT S.nextId b1.done.nextId a1.done.news b2.done.news,
          newsEqT a1.done.nextId S.nextId a2.done.news b1.done.news, ownsEqT a1.done.owns b2.done.owns,
          ownsEqT a2.done.owns b1.done.owns])) := by
      by_cases ha : Holds M a2.fault <;> by_cases hb' : Holds M b2.fault
      · exact .inl ⟨ha, hb'⟩
      · exact absurd (fun hna _ => absurd ha hna) (hv fun _ => hb')
      · exact absurd (fun _ hnb => absurd hb' hnb) (hv fun h => absurd h ha)
      · exact .inr ⟨ha, hb', Classical.byContradiction fun hs => hv (fun h => absurd h ha) fun _ _ => hs⟩
    rcases key with ⟨ha2, hb2⟩ | ⟨ha2, hb2, hsame⟩
    · obtain ⟨g2, hg2⟩ := Option.isSome_iff_exists.1 ((fault_true hfA2).1 ha2)
      obtain ⟨g4, hg4⟩ := Option.isSome_iff_exists.1 ((fault_true hfC2).1 hb2)
      rw [hg2] at hA2
      rw [hg4] at hC2
      simp only at hA2 hC2
      rw [hA2, hC2]
      exact .inr ⟨trivial, trivial⟩
    · have hg2 : ko2.fault? M = none := Option.not_isSome_iff_eq_none.1 fun h => ha2 ((fault_true hfA2).2 h)
      have hg4 : ko4.fault? M = none := Option.not_isSome_iff_eq_none.1 fun h => hb2 ((fault_true hfC2).2 h)
      rw [hg2] at hA2
      rw [hg4] at hC2
      simp only at hA2 hC2
      simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsame
      obtain ⟨hrq, htq, he14, he23, hn14, hn23, ho14, ho23⟩ := hsame
      obtain ⟨r1, m1, fr1, ev1, effs1, os1, hW1, -, -, -, -, hN1, -, hO1, hev1⟩ := hA1
      obtain ⟨r2, m2, fr2, ev2, effs2, os2, hW2, hr2, hm2, -, -, hN2, -, hO2, hev2⟩ := hA2
      obtain ⟨r3, m3, fr3, ev3, effs3, os3, hW3, -, -, -, -, hN3, -, hO3, hev3⟩ := hC1
      obtain ⟨r4, m4, fr4, ev4, effs4, os4, hW4, hr4, hm4, -, -, hN4, -, hO4, hev4⟩ := hC2
      obtain ⟨psA1, psC1, hwA1, hwC1, hP1⟩ := news_same hN1 hN4 hR.nextId hcn hn14
      obtain ⟨psA2, psC2, hwA2, hwC2, hP2⟩ := news_same hN2 hN3 hbn hR.nextId hn23
      obtain rfl := Except.ok.inj (hW1 psA1 hwA1)
      obtain rfl := Except.ok.inj (hW3 psC2 hwC2)
      have hqA := Step.runOwn_queue T chk.reach _ hinvb hqb x2 (hW2 psA2 hwA2)
      have hqd := Step.runOwn_queue T chk.reach _ hinvc hqc x1 (hW4 psC1 hwC1)
      have hO14 := owns_same chk.sites hO1 hO4 ho14 (fun x hx => hqb x (List.mem_append_right _ hx))
        (fun x hx => hqd x (List.mem_append_right _ hx))
      have hO23 := owns_same chk.sites hO2 hO3 ho23 (fun x hx => hqA x (List.mem_append_right _ hx))
        (fun x hx => hqc x (List.mem_append_right _ hx))
      have hfb := Step.runOwn_fresh T hb
      have hfa := Step.runOwn_fresh T (hW2 psA2 hwA2)
      have hl1 := hP1.length_eq
      have hl2 := hP2.length_eq
      have hiA1 := writes_ids hwA1
      have hiA2 := writes_ids hwA2
      have hiC1 := writes_ids hwC1
      have hiC2 := writes_ids hwC2
      rw [hW2 psA2 hwA2, hW4 psC1 hwC1]
      simp only at hfa hfb hiA2 hiC1 hP1 hP2 ⊢
      have h0 := (hsa PBij.refl fun _ _ => rfl).1
      have hob := h0.2.2.2.1
      have hpb := hinv.below
      have hfix : ∀ {m k i : Nat}, i < a0.state.nextId → wireSwap a0.state.nextId m k i = i := fun h => by
        unfold wireSwap; split <;> (try split) <;> omega
      refine .inl ?_
      simp only [Diamond.Lift, pure, Except.pure]
      refine (same_of_parts h0 (rel0_of_eqFn v.records_data chk.recordsComparable hr2 hr4 hrecEq hrq)
        (machines_of_eq v.machines chk.machinesComparable hm2 hm4 htabEq htq) (PA := psA1 ++ psA2)
        (PC := (psC2 ++ psC1).map fun p => { p with id := (wireSwap a0.state.nextId (a0.state.nextId + psC2.length)
          (a0.state.nextId + psC2.length + psC1.length)) p.id })
        (OA := os1 ++ os2) (OC := os3 ++ os4) (EA := ev1 ++ ev2) (EC := ev3 ++ ev4) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ((hO14.append hO23).perm_right List.perm_append_comm) ?_ ?_ ?_ ?_)
      · exact List.append_assoc _ _ _
      · simp only [Step.Acc.mapWire, List.append_assoc, List.map_append]
        exact congrArg (· ++ _) (map_self fun p hp => by simp only [hfix (hpb p hp)])
      · have h1 := hP1.imp_mem (r' := fun p q => p.id = wireSwap a0.state.nextId (a0.state.nextId + psC2.length)
            (a0.state.nextId + psC2.length + psC1.length) q.id ∧ PendingAlike PBij.refl p q) fun p hp q hq h => by
          refine ⟨?_, h.2⟩
          have := hiC1 q hq
          unfold wireSwap; split <;> (try split) <;> omega
        have h2 := hP2.imp_mem (r' := fun p q => p.id = wireSwap a0.state.nextId (a0.state.nextId + psC2.length)
            (a0.state.nextId + psC2.length + psC1.length) q.id ∧ PendingAlike PBij.refl p q) fun p hp q hq h => by
          refine ⟨?_, h.2⟩
          have := hiC2 q hq
          unfold wireSwap; split <;> (try split) <;> omega
        rw [List.map_append]
        exact ((multi_rewire h1).append (multi_rewire h2)).perm_right List.perm_append_comm
      · intro p hp
        rcases List.mem_append.1 hp with h | h
        · have := hiA1 p h; dsimp only at this ⊢; omega
        · have := hiA2 p h; dsimp only at this ⊢; omega
      · rfl
      · rfl
      · simp only [Step.Acc.mapWire]; omega
      · dsimp only; omega
      · simp [List.append_assoc]
      · simp only [Step.Acc.mapWire, List.append_assoc, List.map_append, List.map_map]
        exact congrArg (· ++ _) (map_self fun o ho => by simp only [hfix (hob o ho)])
      · exact List.append_assoc _ _ _
      · simp [Step.Acc.mapWire, List.append_assoc]
      · simp [List.append_assoc]
      · simp [Step.Acc.mapWire, List.append_assoc]
      · exact (Multi.of_forall2 (forall2_append (events_of_slotsEq hev1 hev4 he14)
          (events_of_slotsEq hev2 hev3 he23))).perm_right List.perm_append_comm
      · simp only [Step.Acc.mapWire]; omega
  · revert hC1
    cases hko3 : ko3.fault? M with
    | none =>
      intro hC1
      obtain ⟨_, ha'⟩ := hC1.ok
      rw [hg] at ha'
      cases ha'
    | some g3 =>
    intro _
    have hfb1 : Holds M b1.fault := by rw [fault_true hfC1, hko3]; rfl
    simp only [holds_and, holds_or, holds_not, not_and, not_or, Classical.not_not] at hviol
    have ha2 : Holds M a2.fault := (hviol hfa1).1 hfb1
    obtain ⟨g2, hg2⟩ := Option.isSome_iff_exists.1 ((fault_true hfA2).1 ha2)
    rw [hg2] at hA2
    simp only at hA2
    rw [hA2]
    trivial
/-- Every internal step a pair's two orders run fits the slots: each effect where it runs first, and each after the
other one ran to its end. -/
def PairFits (S : Ty → Nat) (T : List TypeDecl) (a0 : Step.Acc v) (e1 e2 : OwnEffectV v.event) : Prop :=
  ownFits S T a0.state e1 ∧ ownFits S T (a0.withFresh (a0.state.fresh + 1)).state e2 ∧
    (∀ b, Step.runOwn T a0 e1 = .ok b → ownFits S T b.state e2) ∧
    ∀ c, Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) e2 = .ok c →
      ownFits S T (c.withFresh a0.state.fresh).state e1

/-- A pair question's condition holds exactly when every internal step the two orders run fits the slots, where the
codes' condition holds: what makes its bound question honest. -/
theorem pair_fits {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) {S : SymState v} {a0 : Step.Acc v} (hR : StateRel M L T (shapes v) S a0.state)
    (hinv : Step.Inv P a0.state) (hqk : Step.QueueOk P a0) {t1 t2 : Term} {x1 x2 : OwnEffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (t1.denote M)) (hx2 : RelV L (.dsl .effect [v.event]) x2.effect (t2.denote M))
    (hreach1 : x1.effect.Reach P) (hreach2 : x2.effect.Reach P)
    {k1 k2 : OwnPlace L v.event} (ht1 : Holds M (.is senv.dE (L.ownCtor v.event k1) t1))
    (ht2 : Holds M (.is senv.dE (L.ownCtor v.event k2) t2))
    {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o) (hcodes : Holds M o.codes) :
    Holds M o.cond ↔ PairFits L.count T a0 x1 x2 := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko1, a1⟩, c1, y1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko2, a2⟩, c2, y2⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko3, b1⟩, c3, y3⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko4, b2⟩, c4, y4⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨recEq, -, henc⟩ := bind_ok.1 henc
  obtain ⟨tabEq, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcodes ⊢
  obtain ⟨hca, hy1, hy2, hy3, hy4⟩ := hcodes
  have hshs : ∀ sh ∈ shapes v, sh.InSites P := fun _ => shapes_inSites chk.reach
  obtain ⟨vals1, he1, hk1⟩ := own_key hx1 ht1 rfl
  obtain ⟨vals2, he2, hk2⟩ := own_key hx2 ht2 rfl
  have hq0 : (Term.int 0).denote M = .int ((0 : Nat) : Int) := rfl
  have eA1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0
    hR.machines x1 hreach1 he1 hk1 h1 hy1
  have hfr1 : (Term.add S.fresh (.int 1)).denote M =
      .int (Int.ofNat (a0.withFresh (a0.state.fresh + 1)).state.fresh) := by
    simp only [Term.denote, hR.fresh, Val.toInt, Step.Acc.withFresh]; push_cast; rfl
  have eC1 := ownKind_encode chk hshs (shapesHold_shapes v) (a0.withFresh (a0.state.fresh + 1)) happ hca senv
    hR.records hR.now hfr1 hR.nextId hq0 hR.machines x2 hreach2 he2 hk2 h3 hy3
  -- Where the first step of an order holds its condition, its fault term says whether it faults, and where it runs
  -- to its end the second step's condition is exact from there.
  have second1 : Holds M c1 → (Holds M a1.fault ↔ ∃ g, Step.runOwn T a0 x1 = .error g) ∧
      ∀ b, Step.runOwn T a0 x1 = .ok b → (Holds M c2 ↔ ownFits L.count T b.state x2) := fun hc1 => by
    obtain ⟨hfA1, hA1⟩ := eA1.2 hc1
    revert hA1
    cases hko1 : ko1.fault? M with
    | some g =>
      intro hA1
      refine ⟨⟨fun _ => ⟨g, hA1⟩, fun _ => by rw [fault_true hfA1, hko1]; rfl⟩, fun b hb => ?_⟩
      rw [hA1] at hb; cases hb
    | none =>
      intro hA1
      refine ⟨⟨fun h => by rw [fault_true hfA1, hko1] at h; simp at h, fun ⟨g, hg⟩ => ?_⟩, fun b hb => ?_⟩
      · obtain ⟨_, hb⟩ := hA1.ok; rw [hb] at hg; cases hg
      rw [hb] at hA1
      obtain ⟨hbr, hbm, hbf, hbn, hbnow, _, -, hbq, -⟩ := hA1.ends
      have hqb := Step.runOwn_queue T chk.reach a0 hinv hqk x1 hb
      exact (ownKind_encode chk hshs (shapesHold_shapes v) b happ hca senv hbr (hR.now.trans (by rw [hbnow])) hbf hbn
        hbq hbm x2 hreach2 he2 hk2 h2 hy2).1
  have second3 : Holds M c3 → (Holds M b1.fault ↔ ∃ g, Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) x2 = .error g) ∧
      ∀ c, Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) x2 = .ok c →
        (Holds M c4 ↔ ownFits L.count T (c.withFresh a0.state.fresh).state x1) := fun hc3 => by
    obtain ⟨hfC1, hC1⟩ := eC1.2 hc3
    revert hC1
    cases hko3 : ko3.fault? M with
    | some g =>
      intro hC1
      refine ⟨⟨fun _ => ⟨g, hC1⟩, fun _ => by rw [fault_true hfC1, hko3]; rfl⟩, fun c hc => ?_⟩
      rw [hC1] at hc; cases hc
    | none =>
      intro hC1
      refine ⟨⟨fun h => by rw [fault_true hfC1, hko3] at h; simp at h, fun ⟨g, hg⟩ => ?_⟩, fun c hc => ?_⟩
      · obtain ⟨_, hc⟩ := hC1.ok; rw [hc] at hg; cases hg
      rw [hc] at hC1
      obtain ⟨hcr, hcm, -, hcn, hcnow, _, -, hcq, -⟩ := hC1.ends
      have hqc := Step.runOwn_queue T chk.reach (a0.withFresh (a0.state.fresh + 1)) (hinv.congr rfl rfl) hqk x2 hc
      have hff : S.fresh.denote M = .int (Int.ofNat (c.withFresh a0.state.fresh).state.fresh) := by
        simp only [Step.Acc.withFresh]; rw [hR.fresh]
      have hnow' : S.now.denote M = .int (c.withFresh a0.state.fresh).state.now := by
        simp only [Step.Acc.withFresh] at hcnow ⊢; rw [hcnow]; exact hR.now
      exact (ownKind_encode chk hshs (shapesHold_shapes v) (c.withFresh a0.state.fresh) happ hca senv hcr
        hnow' hff hcn hcq hcm x1 hreach1 he1 hk1 h4 hy4).1
  have ite_iff : ∀ {f g : Term} {P Q : Prop}, (Holds M f ↔ P) → (¬ P → (Holds M g ↔ Q)) →
      (Holds M (.ite f tt g) ↔ (¬ P → Q)) := fun {f g P Q} hf hg => by
    rw [holds_ite]
    by_cases hp : Holds M f
    · simp only [show (f.denote M).toBool = true from hp, ↓reduceIte]
      exact ⟨fun _ hn => absurd (hf.1 hp) hn, fun _ => holds_tt⟩
    · have hb : (f.denote M).toBool = false := by simpa [Holds] using hp
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hnp : ¬ P := fun h => hp (hf.2 h)
      exact ⟨fun h _ => (hg hnp).1 h, fun h => (hg hnp).2 (h hnp)⟩
  constructor
  · rintro ⟨hc1, hc3, hc2, hc4⟩
    obtain ⟨hf1, hs1⟩ := second1 hc1
    obtain ⟨hf3, hs3⟩ := second3 hc3
    refine ⟨(eA1.1).1 hc1, (eC1.1).1 hc3, fun b hb => (hs1 b hb).1 ?_, fun c hc => (hs3 c hc).1 ?_⟩
    · have := (ite_iff hf1 fun _ => Iff.rfl (a := Holds M c2)).1 hc2
      exact this fun ⟨g, hg⟩ => by rw [hb] at hg; cases hg
    · have := (ite_iff hf3 fun _ => Iff.rfl (a := Holds M c4)).1 hc4
      exact this fun ⟨g, hg⟩ => by rw [hc] at hg; cases hg
  · rintro ⟨hp1, hp3, hp2, hp4⟩
    have hc1 := (eA1.1).2 hp1
    have hc3 := (eC1.1).2 hp3
    obtain ⟨hf1, hs1⟩ := second1 hc1
    obtain ⟨hf3, hs3⟩ := second3 hc3
    refine ⟨hc1, hc3, (ite_iff hf1 fun _ => Iff.rfl).2 fun hn => ?_, (ite_iff hf3 fun _ => Iff.rfl).2 fun hn => ?_⟩
    · cases hr : Step.runOwn T a0 x1 with
      | error g => exact absurd ⟨g, hr⟩ hn
      | ok b => exact (hs1 b hr).2 (hp2 b hr)
    · cases hr : Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) x2 with
      | error g => exact absurd ⟨g, hr⟩ hn
      | ok c => exact (hs3 c hr).2 (hp4 c hr)

/-- What a pair question's codes condition says: `apply` fits, and so do the functions of each of the two own kinds
the question names. -/
def PairCodesFit (L : Layout) (P : List AnySite) (v : ServiceV) (k1 k2 : OwnPlace L v.event) : Prop :=
  (v.apply.fits L.count).1 ∧ ∀ k ∈ [k1, k2], ownCodesFit L.count (ownShape v P (L.ownsOf v.event)[k])

theorem pair_codes {P : List AnySite} {senv : StepEnv L (shapes v)} {S : SymState v} {t1 t2 : Term}
    {k1 k2 : OwnPlace L v.event} {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o) :
    Holds M o.codes ↔ PairCodesFit L P v k1 k2 := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    (v.apply.code_exact (M := M) happ).1, ownKind_codes h1, ownKind_codes h2, ownKind_codes h3, ownKind_codes h4,
    PairCodesFit]
  exact ⟨fun ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c, c, b⟩⟩

/-- What a pair line's answers say, whichever verdict it reads: its target question is unsat, and its bound question is
unsat (`Prove.proved`) or its codes fit and `F` holds, the fit of the steps the line's scope names
(`Prove.withinBounds`). -/
def PairLine (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))
    (F : Prop) (p : OwnPlace L v.event × OwnPlace L v.event) : Prop :=
  ∃ bq tq, pairQuestions L T P v senv p.1 p.2 = .ok (bq, tq) ∧ Unsat L tq ∧
    (Unsat L bq ∨ PairCodesFit L P v p.1 p.2 ∧ F)

theorem PairLine.mono {P : List AnySite} {senv : StepEnv L (shapes v)} {F G : Prop} (h : F → G) {p : OwnPlace L v.event × OwnPlace L v.event} :
    PairLine L T P v senv F p → PairLine L T P v senv G p
  | ⟨bq, tq, hq, ht, hb⟩ => ⟨bq, tq, hq, ht, hb.imp_right fun ⟨hc, hf⟩ => ⟨hc, h hf⟩⟩

/-- A pair's questions at a model of their variables whose state is one a pair question assumes (pending ids below
the next id, names below the counter) and whose effect variables hold the pair's kinds: the questions' context holds,
so an unsat bound question makes the codes and the condition hold, and an unsat target question leaves only orders
that agree. -/
theorem pair_unfold {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hL : SortedLayout L)
    (senv : StepEnv L (shapes v))
    {k1 k2 : OwnPlace L v.event} {bq tq : TypedScript} (hq : pairQuestions L T P v senv k1 k2 = .ok (bq, tq))
    (hM : ∀ n (h : n < (pairTys v).length), VarSorted L (pairTys v)[n] (M.vars n))
    (hsel : LayoutSel L M) {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hbelow : ∀ p ∈ s.pending, p.id < s.nextId) (hsupp : Step.StateSupp s)
    {x1 x2 : OwnEffectV v.event} (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (M.vars (pairVar v)))
    (hx2 : RelV L (.dsl .effect [v.event]) x2.effect (M.vars (pairVar v + 1)))
    (ht1 : Holds M (.is senv.dE (L.ownCtor v.event k1) (.var (pairVar v))))
    (ht2 : Holds M (.is senv.dE (L.ownCtor v.event k2) (.var (pairVar v + 1))))
    (hreach1 : x1.effect.Reach P) (hreach2 : x2.effect.Reach P) :
    ∃ o, encodePair L T P v senv (SymState.vars 0) (.var (pairVar v)) (.var (pairVar v + 1)) k1 k2 = .ok o ∧
      (Unsat L bq → Holds M o.codes ∧ Holds M o.cond) ∧
      (Unsat L tq → Holds M o.codes → Holds M o.cond → ¬ Holds M o.viol) := by
  obtain ⟨o, ho, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, hbl, hq⟩ := bind_ok.1 hq
  obtain ⟨names, hnames, hq⟩ := bind_ok.1 hq
  obtain ⟨w1, hw1, hq⟩ := bind_ok.1 hq
  obtain ⟨w2, hw2, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, hdts, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hR := decode_state hS
  have hf1 := ownFound_of_reach senv.hE hx1 ht1 hreach1
  have hf2 := ownFound_of_reach senv.hE hx2 ht2 hreach2
  have hpre : ∀ a ∈ [wf, below, names] ++ [Term.is senv.dE (L.ownCtor v.event k1) (.var (pairVar v)),
      .is senv.dE (L.ownCtor v.event k2) (.var (pairVar v + 1))] ++ [w1, w2] ++
      (if ownFound P L v.event k1 && ownFound P L v.event k2 then [] else [Term.bool false]), Holds M a := by
    simp only [hf1, hf2, Bool.and_self, ite_true, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact wf_of_decodeState (need_ok.1 hwf) hS
    · exact (pendingBelow_iff hR.pending hR.nextId hbl).2 hbelow
    · exact stateSupp_names hR hsupp chk.recordsComparable chk.machinesComparable (need_ok.1 hnames)
    · exact ht1
    · exact ht2
    · exact ownWf_holds hL senv.hE hx1 ht1 (need_ok.1 hw1)
    · exact ownWf_holds hL senv.hE hx2 ht2 (need_ok.1 hw2)
  refine ⟨o, ho, fun hbq => ?_, fun htq hc hd hv => ?_⟩
  · obtain ⟨a, ha, hna⟩ := hbq.noModel M hM (hsel _ (need_ok.1 hdts))
    rcases List.mem_append.1 ha with ha | ha
    · exact (hna (hpre a ha)).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    simp only [holds_or, holds_not, not_or, Classical.not_not] at hna
    exact hna
  · obtain ⟨a, ha, hna⟩ := htq.noModel M hM (hsel _ (need_ok.1 hdts))
    rcases List.mem_append.1 ha with ha | ha
    · exact hna (hpre a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hna hc
    · exact hna hd
    · exact hna hv

/-- Two own effects a model codes are effects of a listed pair of own kinds, whose tests the model's effect variables
pass (T5b, `ownPairs_complete`). -/
theorem pair_kinds (senv : StepEnv L (shapes v)) {x1 x2 : OwnEffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (M.vars (pairVar v)))
    (hx2 : RelV L (.dsl .effect [v.event]) x2.effect (M.vars (pairVar v + 1))) :
    ∃ p ∈ L.ownPairs v.event, Holds M (.is senv.dE (L.ownCtor v.event p.1) (.var (pairVar v))) ∧
      Holds M (.is senv.dE (L.ownCtor v.event p.2) (.var (pairVar v + 1))) := by
  obtain ⟨p, hp, d, n, vals1, vals2, hd, hz1, hz2⟩ := ownPairs_complete hx1 hx2
  obtain rfl := find_det hd senv.hE
  have htest : ∀ (j : OwnPlace L v.event) (vals : List Val) (i : Nat), M.vars i = .ctor senv.dE (L.ownCtor v.event j) vals →
      Holds M (.is senv.dE (L.ownCtor v.event j) (.var i)) := fun j vals i h => by
    simp [Holds, Term.denote, h, Val.toBool]
  exact ⟨p, hp, htest _ _ _ hz1, htest _ _ _ hz2⟩

/-- T5's pair hypothesis from a pair line: where it reads proved, or within the bounds and the two orders fit the
slots, the two effects of the pair's kinds commute from every step in progress whose state a model's values decode
to, with its pending ids below its next id and its names below its counter, and which relates to itself under every
renaming keeping its counters. -/
theorem pair_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hL : SortedLayout L)
    (senv : StepEnv L (shapes v))
    {a0 : Step.Acc v} {x1 x2 : OwnEffectV v.event} {k1 k2 : OwnPlace L v.event}
    (hl : PairLine L T P v senv (PairFits L.count T a0 x1 x2) (k1, k2))
    (hM : ∀ n (h : n < (pairTys v).length), VarSorted L (pairTys v)[n] (M.vars n)) (hsel : LayoutSel L M)
    (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some a0.state)
    (hbelow : ∀ p ∈ a0.state.pending, p.id < a0.state.nextId) (hsupp : Step.StateSupp a0.state)
    (hqk : Step.QueueOk P a0) (hsa : Below Step.Acc.Self a0.state.fresh a0)
    (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (M.vars (pairVar v)))
    (hx2 : RelV L (.dsl .effect [v.event]) x2.effect (M.vars (pairVar v + 1)))
    (hreach1 : x1.effect.Reach P) (hreach2 : x2.effect.Reach P)
    (ht1 : Holds M (.is senv.dE (L.ownCtor v.event k1) (.var (pairVar v))))
    (ht2 : Holds M (.is senv.dE (L.ownCtor v.event k2) (.var (pairVar v + 1)))) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨bq, tq, hq, htq, hbq⟩ := hl
  obtain ⟨o, ho, hb, ht⟩ := pair_unfold chk hL senv hq hM hsel hS hbelow hsupp hx1 hx2 ht1 ht2 hreach1 hreach2
  have hR := decode_state hS
  have hinv := decode_inv chk.reach hS hbelow
  have hcc : Holds M o.codes ∧ Holds M o.cond := hbq.elim hb fun ⟨hc, hf⟩ =>
    have hcodes := (pair_codes ho).2 hc
    ⟨hcodes, (pair_fits chk senv hR hinv hqk hx1 hx2 hreach1 hreach2 ht1 ht2 ho hcodes).2 hf⟩
  exact pair_commutes chk senv hR hinv hqk hsa (t1 := .var (pairVar v)) (t2 := .var (pairVar v + 1)) hx1 hx2
    hreach1 hreach2 ht1 ht2 ho hcc.1 hcc.2 (ht htq hcc.1 hcc.2)

end

end Tazuna.Smt
