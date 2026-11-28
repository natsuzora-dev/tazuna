import Tazuna.Smt.PairCompare
import Tazuna.Smt.Cti
import Tazuna.Smt.InternalDispatch
import Tazuna.Smt.Names
import Tazuna.Semantics.PairCommute
import Tazuna.Smt.DecodeRel

/-! The question T5 asks of a listed pair of own kinds (`Step.PairCommutes`, `Layout.ownPairs`): from a symbolic state,
the first effect runs then the second (order A), each internal step encoded for its kind, and A is compared with the
other order. The two orders commute when the first does not fault, or when the second faults first and still faults
after it, or when both orders fault, or when A's result is the other order's up to renaming the names the pair made
(`Step.Same`). That renaming keeps or swaps the pair's two counters and maps the wire ids the pair sent one to one, so
the question compares A with two runs of the other order, each with every counter kept: the canonical order, where
each effect gets the counter it gets in A (`Step.canonPair`), and the actual one, where each gets the counter it gets
running in that order, which is the canonical order with the two counters swapped (`Step.actual_canon`). Each
comparison reads records and instance tables by Gleam's `==` and the events, requests and own effects of both steps
as multisets of their codes, a request without its wire id (`sameT`), as `Same` reads them, so no renaming is searched
for (`pair_sound`) and a model is two orders that end differently under every renaming of the pair's counters.

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

/-- Two internal steps in turn as one: the second's records, tables, next id and queue place, and the news, own and
event slots of both (`AccRel.bind`). -/
def EventsOut.join {v : ServiceV} (o1 o2 : EventsOut v) : EventsOut v :=
  { o2 with news := o1.news ++ o2.news, owns := o1.owns ++ o2.owns, events := o1.events ++ o2.events }

/-- Whether two runs from one state end the same with every counter kept: records and instance tables by Gleam's
`==`, and the events applied, the requests sent and the own commands and queries queued as multisets of their codes,
a request without its wire id and an own effect without its place in the queue (`rel_of_runs`). -/
def sameT (o o' : EventsOut v) : Except Refusal Term := do
  let recEq ← eqFn L v.records
  let tabEq ← tablesEqT L v.machines o.tables o'.tables
  pure (allT [recEq o.records o'.records, tabEq, bagEqT .eq (shareSlots o.events) (shareSlots o'.events),
    bagEqT .eq (shareSlots (seconds (o.news.map (·.slot)))) (shareSlots (seconds (o'.news.map (·.slot)))),
    bagEqT .eq (shareSlots (seconds (o.owns.map (·.slot)))) (shareSlots (seconds (o'.owns.map (·.slot))))])

/-- The pair of own kinds `k1`, `k2` (places among the own kinds) from the symbolic state `S`, with the effects
`e1` and `e2`: order A (`e1` then `e2`), the canonical other order (`e2` at the next counter, then `e1` at the
current one) and the actual other order (`e2` then `e1`, each at the counter it gets). The other order ends the same
as A where A's result matches the canonical order's or the actual order's with every counter kept and the wire ids
matched one to one: those are the two renamings of the pair's counters (`Step.Same`), the actual order standing for
the canonical one with the two counters swapped (`Step.actual_canon`). -/
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
  let ⟨⟨_, d1⟩, c5, _⟩ ← step S.records S.fresh S.nextId (.int 0) e2 S.machines k2 key2
  let ⟨⟨_, d2⟩, c6, _⟩ ← step d1.done.records d1.fresh d1.done.nextId d1.done.queued e1 d1.done.tables k1 key1
  let sameC ← sameT L v (a1.done.join a2.done) (b1.done.join b2.done)
  let sameD ← sameT L v (a1.done.join a2.done) (d1.done.join d2.done)
  let agree := Term.or (.and a2.fault b2.fault) (.and (.not a2.fault)
    (.or (.and (.not b2.fault) sameC) (allT [c5, c6, .not d1.fault, .not d2.fault, sameD])))
  let viol := Term.and (.not a1.fault) (.or (.and b1.fault (.not a2.fault)) (.and (.not b1.fault) (.not agree)))
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

/-- Whether no input kind's cascade can have effects of the own kinds `k1` and `k2` waiting together (`together`): no
step ever runs the two in either order, so the pair needs no question and its line reads proved (`PairOk`). -/
def Layout.apart (k1 k2 : OwnPlace L v.event) : Bool :=
  !together P (stepInputs v (shapes v) senv.nT (stateWidth v)) (L.ownsOf v.event)[k1].answer.site
    (L.ownsOf v.event)[k2].answer.site

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
      exact ⟨hm.1, hm.2⟩
    exact ⟨insts_of_table (rel0_of_eqFn m.table_data htc hta htb hf hh.1),
      machines_of_eq ms (fun m' hm' => hc m' (List.mem_cons_of_mem _ hm')) ha hb hc' hh.2⟩

theorem fault_true {t : Term} {o : Option Fault} (h : t.denote M = .bool o.isSome) : Holds M t ↔ o.isSome := by
  simp [Holds, h, Val.toBool]

/-- Two runs from `a0` whose results `sameT` finds the same end related with every counter kept and the wire ids
they sent matched one to one, every wire id below `a0`'s next one kept. -/
theorem rel_of_runs {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) {a0 A X : Step.Acc v}
    (h0 : Step.Acc.Rel ⟨PBij.refl, PBij.refl⟩ a0 a0) {oA oX : EventsOut v} {fA fX : Term}
    (hA : AccRel M L T (shapes v) a0 oA fA 0 (.ok A)) (hX : AccRel M L T (shapes v) a0 oX fX 0 (.ok X))
    {c : Term} (hc : sameT L v oA oX = .ok c) (hs : Holds M c) (hqA : Step.QueueOk P A) (hqX : Step.QueueOk P X) :
    ∃ W : PBij, (∀ i < a0.state.nextId, W.rel i i) ∧ Step.Acc.Rel ⟨PBij.refl, W⟩ A X ∧
      A.state.nextId = X.state.nextId ∧ a0.state.nextId ≤ A.state.nextId := by
  obtain ⟨recEq, hrecEq, hc⟩ := bind_ok.1 hc
  obtain ⟨tabEq, htabEq, hc⟩ := bind_ok.1 hc
  cases pure_ok.1 hc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨hrq, htq, hev, hnews, hown⟩ := hs
  obtain ⟨recsA, msA, frA, evsA, effsA, osA, hWA, hrA, hmA, -, -, hNA, -, hOA, hevA⟩ := hA
  obtain ⟨recsX, msX, frX, evsX, effsX, osX, hWX, hrX, hmX, -, -, hNX, -, hOX, hevX⟩ := hX
  obtain ⟨psA, psX, hwA, hwX, hP⟩ := news_multi hNA hNX hnews
  cases Except.ok.inj (hWA psA hwA)
  cases Except.ok.inj (hWX psX hwX)
  obtain ⟨⟨-, -, hp, -, hb, -⟩, hev0, hout, ho, -, hown0⟩ := h0
  have hlen : psA.length = psX.length := by
    obtain ⟨zs, hz, hzp⟩ := hP
    rw [forall2_length hz, hzp.length_eq]
  have hrange {ps : List (Step.Pending v.event)} (h : ps.map (·.id) = List.range' a0.state.nextId ps.length) :
      ∀ p ∈ ps, a0.state.nextId ≤ p.id ∧ p.id < a0.state.nextId + ps.length := fun p hp => by
    have := List.mem_map_of_mem (f := (·.id)) hp
    rw [h, List.mem_range'_1] at this
    exact this
  have hidA := writes_ids_range hwA
  have hidX := writes_ids_range hwX
  obtain ⟨W, -, hfix, -, hPW⟩ := wire_match (n0 := a0.state.nextId) hP (by rw [hidA]; exact List.nodup_range')
    (by rw [hidX]; exact List.nodup_range') (fun p hp => (hrange hidA p hp).1) (fun p hp => (hrange hidX p hp).1)
  have hpend : Multi (Step.Pending.Rel ⟨PBij.refl, W⟩) a0.state.pending a0.state.pending :=
    hp.imp_mem fun p hp' q _ h => ⟨by have e : p.id = q.id := h.1; rw [← e]; exact hfix _ (hb p hp'), h.2⟩
  have houts : Multi (Step.OutLine.Rel ⟨PBij.refl, W⟩) a0.out a0.out :=
    hout.imp_mem fun o ho' o' _ h => ⟨by have e : o.id = o'.id := h.1; rw [← e]; exact hfix _ (ho o ho'), h.2⟩
  have hbelow {ps : List (Step.Pending v.event)} (h : ps.map (·.id) = List.range' a0.state.nextId ps.length) :
      ∀ p ∈ a0.state.pending ++ ps, p.id < a0.state.nextId + ps.length := fun p hp' =>
    (List.mem_append.1 hp').elim (fun h' => Nat.lt_of_lt_of_le (hb p h') (Nat.le_add_right _ _))
      fun h' => (hrange h p h').2
  have hobelow {ps : List (Step.Pending v.event)} (h : ps.map (·.id) = List.range' a0.state.nextId ps.length) :
      ∀ o ∈ a0.out ++ ps.map Step.Pending.line, o.id < a0.state.nextId + ps.length := fun o ho' =>
    (List.mem_append.1 ho').elim (fun h' => Nat.lt_of_lt_of_le (ho o h') (Nat.le_add_right _ _))
      fun h' => by obtain ⟨p, hp', rfl⟩ := List.mem_map.1 h'; exact (hrange h p hp').2
  refine ⟨W, hfix, ⟨⟨rel0_of_eqFn v.records_data chk.recordsComparable hrA hrX hrecEq hrq,
    machines_of_eq v.machines chk.machinesComparable hmA hmX htabEq htq, hpend.append hPW, PBij.point_of_eq rfl rfl,
    hbelow hidA, hbelow hidX⟩, hev0.append (events_multi hevA hevX hev),
    houts.append (hPW.map fun _ _ h => Step.Pending.rel_line h), hobelow hidA, hobelow hidX,
    hown0.append (owns_multi chk.sites hOA hOX hown (fun x hx => hqA x (List.mem_append_right _ hx))
      (fun x hx => hqX x (List.mem_append_right _ hx)))⟩, by simp [hlen], Nat.le_add_right _ _⟩

/-- An own kind's internal step whose condition holds: its fault term holds exactly when the step faults. -/
theorem fault_iff_of_encode {shs : List (PendingShape v.event)} {a : Step.Acc v} {x : OwnEffectV v.event}
    {ko : OwnKindOut v} {st : StepTerms v} {c : Term} {q0 : Nat}
    (he : Holds M c → st.fault.denote M = .bool (ko.fault? M).isSome ∧
      match ko.fault? M with
      | some f => Step.runOwn T a x = .error f
      | none => AccRel M L T shs a st.done st.fresh q0 (Step.runOwn T a x))
    (hc : Holds M c) : Holds M st.fault ↔ ∃ g, Step.runOwn T a x = .error g := by
  obtain ⟨h1, h2⟩ := he hc
  revert h2
  cases hk : ko.fault? M with
  | some g => intro h2; exact ⟨fun _ => ⟨g, h2⟩, fun _ => by rw [fault_true h1, hk]; rfl⟩
  | none =>
    intro h2
    refine ⟨fun h => by rw [fault_true h1, hk] at h; simp at h, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨_, h3⟩ := h2.ok
    rw [h3] at hg
    cases hg

/-- An own kind's internal step whose condition holds and whose fault term does not runs as its terms say. -/
theorem acc_of_encode {shs : List (PendingShape v.event)} {a : Step.Acc v} {x : OwnEffectV v.event}
    {ko : OwnKindOut v} {st : StepTerms v} {c : Term} {q0 : Nat}
    (he : Holds M c → st.fault.denote M = .bool (ko.fault? M).isSome ∧
      match ko.fault? M with
      | some f => Step.runOwn T a x = .error f
      | none => AccRel M L T shs a st.done st.fresh q0 (Step.runOwn T a x))
    (hc : Holds M c) (hf : ¬ Holds M st.fault) : AccRel M L T shs a st.done st.fresh q0 (Step.runOwn T a x) := by
  obtain ⟨h1, h2⟩ := he hc
  revert h2
  cases hk : ko.fault? M with
  | some g => intro _; exact absurd (by rw [fault_true h1, hk]; rfl) hf
  | none => intro h2; exact h2

/-- A pair question's terms: where the codes' condition and the condition hold and the two orders are not reported as
not commuting, the two effects commute from every step in progress whose state the symbolic state denotes, whose
pending requests and own queue hold kept functions of `P`, and which, with the two effects, relates to itself under
every renaming keeping its counters (`Step.PairCommutes`). Where A's result matches the actual other order's, the
canonical order agrees with it (`Step.actual_canon`). -/
theorem pair_commutes {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hv : v.Equivariant)
    (senv : StepEnv L (shapes v))
    {S : SymState v} {a0 : Step.Acc v} (hR : StateRel M L T (shapes v) S a0.state) (hinv : Step.Inv P a0.state)
    (hqk : Step.QueueOk P a0) (hsa : Below Step.Acc.Self a0.state.fresh a0) {t1 t2 : Term} {x1 x2 : OwnEffectV v.event}
    (hb1 : Below (fun P x => OwnEffectV.Rel P x x) a0.state.fresh x1)
    (hb2 : Below (fun P x => OwnEffectV.Rel P x x) a0.state.fresh x2)
    (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (t1.denote M)) (hx2 : RelV L (.dsl .effect [v.event]) x2.effect (t2.denote M))
    (hreach1 : x1.effect.Reach P) (hreach2 : x2.effect.Reach P)
    {k1 k2 : OwnPlace L v.event} (ht1 : Holds M (.is senv.dE (L.ownCtor v.event k1) t1))
    (ht2 : Holds M (.is senv.dE (L.ownCtor v.event k2) t2))
    {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o)
    (hcodes : Holds M o.codes) (hcond : Holds M o.cond) (hviol : ¬ Holds M o.viol) :
    Step.PairCommutes T a0 x1 x2 := by
  have hac := (Step.actual_canon T hv hsa hb1 hb2).2
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko1, a1⟩, c1, y1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko2, a2⟩, c2, y2⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko3, b1⟩, c3, y3⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko4, b2⟩, c4, y4⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko5, d1⟩, c5, y5⟩, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko6, d2⟩, c6, y6⟩, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨sameC, hsameC, henc⟩ := bind_ok.1 henc
  obtain ⟨sameD, hsameD, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcodes hcond
  obtain ⟨hca, hy1, hy2, hy3, hy4⟩ := hcodes
  obtain ⟨hc1, hc3, hc2, hc4⟩ := hcond
  have hy5 : Holds M y5 := (ownKind_codes h5).2 ((ownKind_codes h3).1 hy3)
  have hy6 : Holds M y6 := (ownKind_codes h6).2 ((ownKind_codes h4).1 hy4)
  have hshs : ∀ sh ∈ shapes v, sh.InSites P := fun _ => shapes_inSites chk.reach
  obtain ⟨vals1, he1, hk1⟩ := own_key hx1 ht1 rfl
  obtain ⟨vals2, he2, hk2⟩ := own_key hx2 ht2 rfl
  have hq0 : (Term.int 0).denote M = .int ((0 : Nat) : Int) := rfl
  have hnowOf : ∀ {b : Step.Acc v}, b.state.now = a0.state.now → S.now.denote M = .int b.state.now := fun h => by
    rw [h]; exact hR.now
  have eA1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0 hR.machines x1 hreach1 he1 hk1 h1 hy1
  have hfr1 : (Term.add S.fresh (.int 1)).denote M =
      .int (Int.ofNat (a0.withFresh (a0.state.fresh + 1)).state.fresh) := by
    simp only [Term.denote, hR.fresh, Val.toInt, Step.Acc.withFresh]; push_cast; rfl
  have eC1 := ownKind_encode chk hshs (shapesHold_shapes v) (a0.withFresh (a0.state.fresh + 1)) happ hca senv
    hR.records hR.now hfr1 hR.nextId hq0 hR.machines x2 hreach2 he2
    hk2 h3 hy3
  have h0 := (hsa PBij.refl ⟨rfl, fun _ _ => rfl⟩).1
  intro b hb
  have hfa1 : ¬ Holds M a1.fault := fun h => by
    obtain ⟨g, hg⟩ := (fault_iff_of_encode eA1.2 hc1).1 h
    rw [hb] at hg; cases hg
  have hc2' : Holds M c2 := by
    rw [holds_ite] at hc2
    simpa [show (a1.fault.denote M).toBool = false by simpa [Holds] using hfa1] using hc2
  have hA1 := acc_of_encode eA1.2 hc1 hfa1
  have hA1b : AccRel M L T (shapes v) a0 a1.done a1.fresh 0 (.ok b) := hb ▸ hA1
  obtain ⟨hbr, hbm, hbf, hbn, hbnow, osb, hbown, hbq, -⟩ := hA1b.ends
  have eA2 := ownKind_encode chk hshs (shapesHold_shapes v) b happ hca senv hbr (hnowOf hbnow) hbf hbn hbq hbm x2 hreach2 he2 hk2 h2 hy2
  have hqb := Step.runOwn_queue T chk.reach a0 hinv hqk x1 hb
  have hinvb := Step.runOwn_inv T chk.reach a0 hinv x1 hb
  have hfb := Step.runOwn_fresh T hb
  have hv1 : ¬ Holds M _ := fun h => hviol ((holds_and _ _).2 ⟨(holds_not _).2 hfa1, h⟩)
  -- Order A, `e1` then `e2`, where its second step does not fault.
  have runA : ¬ Holds M a2.fault → ∃ A, Step.runOwn T b x2 = .ok A ∧
      AccRel M L T (shapes v) a0 (a1.done.join a2.done) a2.fresh 0 (.ok A) ∧ Step.QueueOk P A ∧
      A.state.fresh = a0.state.fresh + 2 := fun hfa2 => by
    have hA2 := acc_of_encode eA2.2 hc2' hfa2
    obtain ⟨A, hA⟩ := hA2.ok
    have hj := AccRel.bind (g := fun b' => Step.runOwn T b' x2) hA1 fun b' os hr hown hrec hms hfr hn hq hO => by
      rw [hb] at hr; cases hr
      obtain rfl : os = osb := List.append_cancel_left (hown.symm.trans hbown)
      exact hA2
    rw [hb] at hj
    refine ⟨A, hA, by unfold EventsOut.join; simpa [bind, Except.bind, hA] using hj, Step.runOwn_queue T chk.reach b hinvb hqb x2 hA, ?_⟩
    rw [Step.runOwn_fresh T hA, hfb]
  refine ⟨fun c hc => ?_, fun g hg => ?_⟩
  · have hfb1 : ¬ Holds M b1.fault := fun h => by
      obtain ⟨g, hg⟩ := (fault_iff_of_encode eC1.2 hc3).1 h
      rw [hc] at hg; cases hg
    have hag := Classical.byContradiction fun h =>
      hv1 ((holds_or _ _).2 (.inr ((holds_and _ _).2 ⟨(holds_not _).2 hfb1, (holds_not _).2 h⟩)))
    simp only [holds_or, holds_and, holds_not, holds_allT, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hag
    have hc4' : Holds M c4 := by
      rw [holds_ite] at hc4
      simpa [show (b1.fault.denote M).toBool = false by simpa [Holds] using hfb1] using hc4
    have hC1 := acc_of_encode eC1.2 hc3 hfb1
    have hC1c : AccRel M L T (shapes v) (a0.withFresh (a0.state.fresh + 1)) b1.done b1.fresh 0 (.ok c) := hc ▸ hC1
    obtain ⟨hcr, hcm, -, hcn, hcnow, osc, hcown, hcq, -⟩ := hC1c.ends
    have hff : S.fresh.denote M = .int (Int.ofNat (c.withFresh a0.state.fresh).state.fresh) := by
      simp only [Step.Acc.withFresh]; rw [hR.fresh]
    have eC2 := ownKind_encode chk hshs (shapesHold_shapes v) (c.withFresh a0.state.fresh) happ hca senv hcr
      (hnowOf (b := c.withFresh a0.state.fresh) (by simpa [Step.Acc.withFresh] using hcnow)) hff hcn hcq hcm
      x1 hreach1 he1 hk1 h4 hy4
    rcases hag with ⟨ha2, hb2⟩ | ⟨ha2, ⟨hb2, hsC⟩ | ⟨hc5, hc6, hfd1, hfd2, hsD⟩⟩
    · -- Both orders fault at their second step.
      obtain ⟨g2, hg2⟩ := (fault_iff_of_encode eA2.2 hc2').1 ha2
      obtain ⟨g4, hg4⟩ := (fault_iff_of_encode eC2.2 hc4').1 hb2
      rw [hg2]
      simp only [Step.canonPair, hc, hg4, bind, Except.bind]
      exact .inr ⟨trivial, trivial⟩
    · -- A's result matches the canonical order's.
      obtain ⟨A, hA, hAacc, hqA, hfA⟩ := runA ha2
      have hC2 := acc_of_encode eC2.2 hc4' hb2
      obtain ⟨Cr, hCr⟩ := hC2.ok
      have hj := AccRel.bind (g := fun c' => Step.runOwn T (c'.withFresh a0.state.fresh) x1) hC1
        fun c' os hr hown hrec hms hfr hn hq hO => by
          rw [hc] at hr; cases hr
          obtain rfl : os = osc := List.append_cancel_left (hown.symm.trans hcown)
          exact AccRel.of_fresh hC2
      rw [hc] at hj
      have hCacc : AccRel M L T (shapes v) a0 (b1.done.join b2.done) b2.fresh 0 (.ok Cr) :=
        AccRel.of_fresh (k := a0.state.fresh + 1)
          (show AccRel M L T (shapes v) (a0.withFresh (a0.state.fresh + 1)) (b1.done.join b2.done) b2.fresh 0 (.ok Cr) by
            unfold EventsOut.join; simpa [bind, Except.bind, hCr] using hj)
      have hqc := Step.runOwn_queue T chk.reach (a0.withFresh (a0.state.fresh + 1)) (hinv.congr rfl rfl) hqk x2 hc
      have hinvc : Step.Inv P (c.withFresh a0.state.fresh).state :=
        (Step.runOwn_inv T chk.reach (a0.withFresh (a0.state.fresh + 1)) (hinv.congr rfl rfl) x2 hc).congr rfl rfl
      have hqCr := Step.runOwn_queue T chk.reach (c.withFresh a0.state.fresh) hinvc hqc x1 hCr
      obtain ⟨W, hfix, hrel, hnext, hle⟩ := rel_of_runs chk h0 hAacc hCacc hsameC hsC hqA hqCr
      have hlt : ∀ i < Cr.state.nextId, wireSwap a0.state.nextId c.state.nextId Cr.state.nextId i < Cr.state.nextId :=
        fun _ h => wireSwap_lt h
      have hrel' := (hrel.withFresh A.state.fresh (a0.state.fresh + 2)).mapWire wireSwap_inj
        (by simpa [Step.Acc.withFresh] using hlt)
      rw [hA]
      simp only [Step.canonPair, hc, hCr, bind, Except.bind, pure, Except.pure]
      refine .inl (.base ⟨_, rfl, hrel', ?_, ?_, ?_, fun _ _ => rfl, fun i hi => ⟨i, hfix i hi, ?_⟩⟩)
      · simp [Step.Acc.mapWire, Step.Acc.withFresh, hfA]
      · simp [Step.Acc.mapWire, Step.Acc.withFresh, hnext]
      · simpa [Step.Acc.withFresh] using hle
      · exact (show wireSwap a0.state.nextId c.state.nextId Cr.state.nextId i = i by
          unfold wireSwap; split <;> (try split) <;> omega).symm
    · -- A's result matches the actual other order's, which agrees with the canonical one.
      obtain ⟨A, hA, hAacc, hqA, hfA⟩ := runA ha2
      have eD1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0 hR.machines x2 hreach2 he2 hk2 h5 hy5
      have hD1 := acc_of_encode eD1.2 hc5 hfd1
      obtain ⟨d, hd⟩ := hD1.ok
      have hD1d : AccRel M L T (shapes v) a0 d1.done d1.fresh 0 (.ok d) := hd ▸ hD1
      obtain ⟨hdr, hdm, hdf, hdn, hdnow, osd, hdown, hdq, -⟩ := hD1d.ends
      have eD2 := ownKind_encode chk hshs (shapesHold_shapes v) d happ hca senv hdr (hnowOf hdnow) hdf hdn hdq hdm x1 hreach1 he1 hk1 h6 hy6
      have hD2 := acc_of_encode eD2.2 hc6 hfd2
      obtain ⟨D, hD⟩ := hD2.ok
      have hj := AccRel.bind (g := fun d' => Step.runOwn T d' x1) hD1 fun d' os hr hown hrec hms hfr hn hq hO => by
        rw [hd] at hr; cases hr
        obtain rfl : os = osd := List.append_cancel_left (hown.symm.trans hdown)
        exact hD2
      rw [hd] at hj
      have hDacc : AccRel M L T (shapes v) a0 (d1.done.join d2.done) d2.fresh 0 (.ok D) := by
        unfold EventsOut.join; simpa [bind, Except.bind, hD] using hj
      have hqd := Step.runOwn_queue T chk.reach a0 hinv hqk x2 hd
      have hinvd := Step.runOwn_inv T chk.reach a0 hinv x2 hd
      have hqD := Step.runOwn_queue T chk.reach d hinvd hqd x1 hD
      obtain ⟨W, hfix, hrel, hnext, hle⟩ := rel_of_runs chk h0 hAacc hDacc hsameD hsD hqA hqD
      have hfD : D.state.fresh = a0.state.fresh + 2 := by
        rw [Step.runOwn_fresh T hD, Step.runOwn_fresh T hd]
      have hsame : Step.Same a0.state.fresh a0.state.nextId A D :=
        .base ⟨⟨PBij.refl, W⟩, rfl, hrel, hfA.trans hfD.symm, hnext, hle, fun _ _ => rfl, hfix⟩
      have h2 := hac d hd
      rw [hD] at h2
      rw [hA]
      exact Diamond.Agree.trans Diamond.Closure.equiv (Or.inl (show Diamond.Lift _ (.ok A) (.ok D) from hsame)) h2
  · have hfb1 : Holds M b1.fault := (fault_iff_of_encode eC1.2 hc3).2 ⟨g, hg⟩
    have ha2 : Holds M a2.fault := Classical.byContradiction fun h =>
      hv1 ((holds_or _ _).2 (.inl ((holds_and _ _).2 ⟨hfb1, (holds_not _).2 h⟩)))
    obtain ⟨g2, hg2⟩ := (fault_iff_of_encode eA2.2 hc2').1 ha2
    rw [hg2]
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
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
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

/-- What a listed pair of own kinds' line says: its answers (`PairLine`), or that the two are apart (`Layout.apart`). -/
def PairOk (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))
    (F : Prop) (p : OwnPlace L v.event × OwnPlace L v.event) : Prop :=
  PairLine L T P v senv F p ∨ L.apart P v senv p.1 p.2 = true

theorem PairOk.mono {P : List AnySite} {senv : StepEnv L (shapes v)} {F G : Prop} (h : F → G)
    {p : OwnPlace L v.event × OwnPlace L v.event} : PairOk L T P v senv F p → PairOk L T P v senv G p :=
  Or.imp_left (PairLine.mono h)

/-- An own effect is answered at the site of the own kind whose variant codes it. -/
theorem OwnKey.holds_site {e : Ty} {key : OwnKey} {x : OwnEffectV e} {vals : List Val} (h : key.Holds L x.effect vals) :
    key.answer.site = x.site := by
  cases key <;> cases x <;> simp only [OwnKey.Holds, OwnEffectV.effect] at h <;>
    first | exact h.elim | exact h.2.2.2.2.1.symm

/-- Effects of two own kinds that some input kind's cascade can have waiting together are of kinds that are not
apart. -/
theorem not_apart {P : List AnySite} (senv : StepEnv L (shapes v)) {k1 k2 : OwnPlace L v.event}
    {x1 x2 : OwnEffectV v.event} {vals1 vals2 : List Val} (h1 : (L.ownsOf v.event)[k1].Holds L x1.effect vals1)
    (h2 : (L.ownsOf v.event)[k2].Holds L x2.effect vals2)
    (hl : ∃ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ∀ l, inp.live P = some l → x1.site ∈ l ∧ x2.site ∈ l) :
    L.apart P v senv k1 k2 = false := by
  obtain ⟨inp, hm, hl⟩ := hl
  simp only [Layout.apart, OwnKey.holds_site h1, OwnKey.holds_site h2, together_of hm hl, Bool.not_true]

/-- A pair's questions at a model of their variables whose state is one a pair question assumes (pending ids below
the next id, names below the counter) and whose effect variables hold the pair's kinds: the questions' context holds,
so an unsat bound question makes the codes and the condition hold, and an unsat target question leaves only orders
that agree. -/
theorem pair_unfold {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hL : SortedLayout L)
    (senv : StepEnv L (shapes v))
    {k1 k2 : OwnPlace L v.event} {bq tq : TypedScript} (hq : pairQuestions L T P v senv k1 k2 = .ok (bq, tq))
    (hM : ∀ n (h : n < (pairTys v).length), VarSorted L (pairTys v)[n] (M.vars n))
    (hsel : LayoutSorted L (pairTys v) M) {s : State v}
    (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
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
  obtain ⟨vars, hvars, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, hdts, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hW := hsel _ _ (need_ok.1 hdts) (mapM_need hvars)
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
  · obtain ⟨a, ha, hna⟩ := hbq.noModel M hM hW
    rcases List.mem_append.1 ha with ha | ha
    · exact (hna (hpre a ha)).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    simp only [holds_or, holds_not, not_or, Classical.not_not] at hna
    exact hna
  · obtain ⟨a, ha, hna⟩ := htq.noModel M hM hW
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
theorem pair_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hv : v.Equivariant)
    (hL : SortedLayout L) (senv : StepEnv L (shapes v))
    {a0 : Step.Acc v} {x1 x2 : OwnEffectV v.event} {k1 k2 : OwnPlace L v.event}
    (hl : PairLine L T P v senv (PairFits L.count T a0 x1 x2) (k1, k2))
    (hM : ∀ n (h : n < (pairTys v).length), VarSorted L (pairTys v)[n] (M.vars n)) (hsel : LayoutSorted L (pairTys v) M)
    (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some a0.state)
    (hbelow : ∀ p ∈ a0.state.pending, p.id < a0.state.nextId) (hsupp : Step.StateSupp a0.state)
    (hqk : Step.QueueOk P a0) (hsa : Below Step.Acc.Self a0.state.fresh a0)
    (hb1 : Below (fun P x => OwnEffectV.Rel P x x) a0.state.fresh x1)
    (hb2 : Below (fun P x => OwnEffectV.Rel P x x) a0.state.fresh x2)
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
  exact pair_commutes chk hv senv hR hinv hqk hsa (t1 := .var (pairVar v)) (t2 := .var (pairVar v + 1)) hb1 hb2 hx1 hx2
    hreach1 hreach2 ht1 ht2 ho hcc.1 hcc.2 (ht htq hcc.1 hcc.2)

end

end Tazuna.Smt
