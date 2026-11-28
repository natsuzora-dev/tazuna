import Tazuna.Semantics.PairCommute

/-! Whether the two orders of a pair of own effects end the same once the names the pair made are renamed, run in
Lean on a counterexample of a pair question. The solver compares A with the other order run with every counter kept
and with the pair's two counters swapped (`sameT`), so its model is one Lean finds different under every renaming,
except where an effect holds a name made from one of those counters (`holdsUnmade`). `sameUpToPair` searches the renamings `Same` allows from the pair's start, which are few: the two counters the pair
used kept or swapped, and the wire ids it sent mapped one to one onto the other order's. Each step in progress is read
as one term (`accTerm`) with collections as sorted lists, as `Ty.canon` reads bags and tables, so equal terms mean the
same values up to the order of multisets.

`Same` compares kept functions by what they do, which no term reads, so the search reads each step twice: with kept
functions by their site and captured values, and with kept functions left out (`dataTerm`). Equal under the first
means the orders end the same; different under the second means they differ in data, which no renaming `Same` allows
can hide (`data_of_same`), so the pair does not commute (`pair_violates`). Between the two, the orders differ only in
which functions they keep, and whether those behave alike is not known. `pairOrders` is the one reading of a pair's
two orders that prove's pair lines and smt-check both use. -/

namespace Tazuna.Smt

open Tazuna.Ir Tazuna.Ir.Step

attribute [local instance] lexOrd

variable {v : ServiceV}

section Terms
variable (σ τ : Nat → Nat) (fn : {t : Ty} → Fun t → Erl)

def siteTerm (s : SiteId) : Erl := .tuple [.bin s.module, .int s.line, .int s.col, .int s.index]

/-- A kept function by its site and captured values. -/
def funTerm {t : Ty} (f : Fun t) : Erl := .tuple [siteTerm f.site, Ty.canonBy σ (.tuple f.Γ) f.env]

def wireTerm (w : WireVal) : Erl := Ty.canonBy σ w.1 w.2

def senderTerm : Sender → Erl
  | .machine n k => .tuple [.bin n, wireTerm σ k]
  | .reaction n => .tuple [.bin n]

/-- A request, with its kept functions read by `fn`. -/
def requestTerm {e : Ty} (r : RequestV e) : Erl :=
  .tuple [.bin r.name, Ty.canonBy σ r.input r.value, .list (r.ensures.toList.map fun f => fn f), fn r.onAnswer]

def ownTerm {e : Ty} : OwnEffectV e → Erl
  | .command n _ i _ value f => .tuple [.atom "command", .bin n, Ty.canonBy σ i value, fn f]
  | .query n _ i _ value f => .tuple [.atom "query", .bin n, Ty.canonBy σ i value, fn f]

def instTerm {r e : Ty} {m : MachineV r e} (i : Instance m) : Erl :=
  .tuple [Ty.canonBy σ m.key i.key, Ty.canonBy σ m.state i.state]

def machinesTerm {r e : Ty} : {ms : List (MachineV r e)} → Machines ms → List Erl
  | [], .nil => []
  | _ :: _, .cons l rest => .list (Erl.sort (l.map (instTerm σ))) :: machinesTerm rest

/-- A step in progress as one term, with fresh ids' counters renamed by `σ`, wire ids by `τ` and kept functions read
by `fn`, and every multiset as a sorted list. -/
def accTerm (a : Acc v) : Erl :=
  .tuple [Ty.canonBy σ v.records a.state.records, .list (machinesTerm σ a.state.machines),
    .list (Erl.sort (a.state.pending.map fun p =>
      .tuple [.int (τ p.id), senderTerm σ p.sender, .bin p.external, requestTerm σ fn p.request])),
    .int a.state.now, .int a.state.fresh, .int a.state.nextId,
    .list (Erl.sort (a.events.map (Ty.canonBy σ v.event))),
    .list (Erl.sort (a.out.map fun o => .tuple [.int (τ o.id), .bin o.external, .bin o.name, wireTerm σ o.input])),
    .list (Erl.sort (a.own.map (ownTerm σ fn)))]

/-- A step in progress as `accTerm` reads it with every kept function left out: what `Same` compares by equality. -/
abbrev dataTerm (a : Acc v) : Erl := accTerm σ τ (fun _ => .atom "") a

end Terms

/-- The wire ids a step in progress holds: its pending requests' and its out lines'. -/
def wireIds (a : Acc v) : List Nat := a.state.pending.map (·.id) ++ a.out.map (·.id)

/-- The wire ids from `n0` on that a step in progress holds. -/
def newIds (n0 : Nat) (a : Acc v) : List Nat := (wireIds a).filter (n0 ≤ ·)

/-- Every one-to-one map of the ids `is` into `avail`, as pairs; an id listed twice is mapped once. -/
def injections : List Nat → List Nat → List (List (Nat × Nat))
  | [], _ => [[]]
  | i :: is, avail =>
    if i ∈ is then injections is avail
    else avail.flatMap fun j => (injections is (avail.erase j)).map ((i, j) :: ·)

/-- The wire id `i` renamed by the pairs `m`; an id `m` does not map is kept. -/
def assignWire (m : List (Nat × Nat)) (i : Nat) : Nat :=
  match m.lookup i with
  | some j => j
  | none => i

/-- The most wire ids a pair may send for `sameUpToPair` to search their renamings. -/
def wireSearchCap : Nat := 7

/-- How `A` and `C`, the two orders of a pair run from a step with the counter `f` and the next wire id `n0`, compare
once the names the pair made are renamed (the counters `f` and `f + 1` kept or swapped, the wire ids from `n0` on
mapped one to one onto `A`'s): the same under one of those renamings; the same data under one but different kept
functions under each; different data under each; or not searched because the pair sent more wire ids than
`wireSearchCap`. -/
inductive Renamed where
  | same
  | keptDiffer
  | differ
  | capped (sends : Nat)

/-- The renamings `sameUpToPair` tries on `C` to meet `A`. -/
def pairRenamings (f n0 : Nat) (A C : Acc v) : List ((Nat → Nat) × (Nat → Nat)) :=
  [id, swapFn f].flatMap fun σ => (injections (newIds n0 C) (newIds n0 A).eraseDups).map fun m => (σ, assignWire m)

def sameUpToPair (f n0 : Nat) (A C : Acc v) : Renamed :=
  let k := C.state.nextId - n0
  if k > wireSearchCap then .capped k else
  let rs := pairRenamings f n0 A C
  if rs.any fun r => accTerm r.1 r.2 (funTerm r.1) C == accTerm id id (funTerm id) A then .same
  else if rs.any fun r => dataTerm r.1 r.2 C == dataTerm id id A then .keptDiffer
  else .differ

/-- How the two orders of a pair of own effects compare, run in Lean from a step in progress: `e1` then `e2`, and the
canonical other order (`Step.canonPair`). -/
inductive PairOrders where
  /-- The second faults alone but not after the first. -/
  | disabled
  /-- One order faults and the other does not. -/
  | faultsInOneOrder
  /-- Both end, with different data under every renaming `sameUpToPair` searches. -/
  | differ
  /-- Both end with the same data up to a renaming, but keep different functions (by site or captured values) under
  each; what those functions do is not compared. -/
  | keptDiffer
  /-- Both end the same up to a renaming of the names the pair made. -/
  | sameUpToRenaming
  /-- The pair sent `sends` wire ids, more than `wireSearchCap`, so no renaming was searched. -/
  | capped (sends : Nat)

/-- Whether the effect holds a name made from the counter `f` or `f + 1`, which a pair's steps make: a model may give
an effect such a name, a waiting effect never holds one. Swapping the two counters changes exactly such an effect's
term. -/
def holdsUnmade {e : Ty} (f : Nat) (x : OwnEffectV e) : Bool :=
  ownTerm (swapFn f) (funTerm (swapFn f)) x != ownTerm id (funTerm id) x

/-- Whether the orders show that the pair does not commute (`pair_violates`): what makes a pair line violated. -/
def PairOrders.violated : PairOrders → Bool
  | .disabled | .faultsInOneOrder | .differ => true
  | .keptDiffer | .sameUpToRenaming | .capped _ => false

/-- The two orders of a pair, or what no counterexample of a pair's target question gives: the first faults, the
second faults in both orders, or both orders fault. -/
def pairOrders (T : List TypeDecl) (a0 : Step.Acc v) (e1 e2 : OwnEffectV v.event) : Except String PairOrders :=
  match Step.runOwn T a0 e1 with
  | .error _ => .error "faults in its first step"
  | .ok b =>
    match Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) e2, Step.runOwn T b e2, Step.canonPair T a0 e1 e2 with
    | .error _, .error _, _ => .error "has the second step fault in both orders"
    | .error _, .ok _, _ => .ok .disabled
    | .ok _, .error _, .error _ => .error "has both orders fault"
    | .ok _, .error _, .ok _ | .ok _, .ok _, .error _ => .ok .faultsInOneOrder
    | .ok _, .ok A, .ok C =>
      .ok (match sameUpToPair a0.state.fresh a0.state.nextId A C with
        | .same => .sameUpToRenaming
        | .keptDiffer => .keptDiffer
        | .differ => .differ
        | .capped n => .capped n)

section Complete

/-! The data search is complete for `Same`: steps in progress that `Same` relates meet in `dataTerm` under one of the
renamings `pairRenamings` lists. `Same` is the closure of `RenamedFrom`, so the proof carries a set of terms that
every step of the closure keeps: each renaming the search may try on one side gives a term some renaming of the other
side gives (`DataCovered`). -/

variable {f n0 : Nat}

/-- A counter renaming the search tries: the two counters a pair uses kept or swapped. -/
def CtrRen (f : Nat) (σ : Nat → Nat) : Prop := σ = id ∨ σ = swapFn f

/-- A wire renaming the search can try on the ids `ids`: those below `n0` kept, the others one to one onto ids from
`n0` on. -/
structure WireRen (n0 : Nat) (ids : List Nat) (τ : Nat → Nat) : Prop where
  below : ∀ i ∈ ids, i < n0 → τ i = i
  above : ∀ i ∈ ids, n0 ≤ i → n0 ≤ τ i
  inj : ∀ i ∈ ids, ∀ j ∈ ids, τ i = τ j → i = j

/-- Each renaming the search may try on `b` gives a term that one it may try on `a` gives. -/
def DataCovered (f n0 : Nat) (a b : Acc v) : Prop :=
  ∀ σ τ, CtrRen f σ → WireRen n0 (wireIds b) τ →
    ∃ σ' τ', CtrRen f σ' ∧ WireRen n0 (wireIds a) τ' ∧ dataTerm σ τ b = dataTerm σ' τ' a

theorem instTerm_rel {R : PBij} {σ σ' : Nat → Nat} (hσ : ∀ {c c'}, R.rel c c' → σ' c = σ c')
    (h0 : R.shift = Option.none) {r e : Ty} {m : MachineV r e} {i j : Instance m} (h : Instance.Rel R i j) :
    instTerm σ' i = instTerm σ j := by
  obtain ⟨hk, hs⟩ := h
  simp only [instTerm, Ty.canonBy_rel hσ h0 _ _ _ hk, Ty.canonBy_rel hσ h0 _ _ _ hs]

theorem machinesTerm_rel {R : PBij} {σ σ' : Nat → Nat} (hσ : ∀ {c c'}, R.rel c c' → σ' c = σ c')
    (h0 : R.shift = Option.none) {r e : Ty} :
    {ms : List (MachineV r e)} → (x y : Machines ms) → Machines.Rel R x y → machinesTerm σ' x = machinesTerm σ y
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, h => by
    have h' : Insts.Rel R _ _ ∧ Machines.Rel R _ _ := h
    simp only [machinesTerm, Multi.sort_map (fun _ _ hij => instTerm_rel hσ h0 hij) h'.1.1,
      machinesTerm_rel hσ h0 _ _ h'.2]

theorem wireTerm_rel {R : PBij} {σ σ' : Nat → Nat} (hσ : ∀ {c c'}, R.rel c c' → σ' c = σ c')
    (h0 : R.shift = Option.none) {x y : WireVal} (h : WireVal.Rel R x y) : wireTerm σ' x = wireTerm σ y := by
  cases h with | mk h => exact Ty.canonBy_rel hσ h0 _ _ _ h

/-- Steps in progress related by `R` with the same counter and next wire id are one data term once each side's names
are renamed so that the names `R` relates meet. -/
theorem dataTerm_rel {R : Ren} {σ σ' τ τ' : Nat → Nat} (hσ : ∀ {c c'}, R.ctr.rel c c' → σ' c = σ c')
    (hτ : ∀ {i j}, R.wire.rel i j → τ' i = τ j) (h0 : R.ctr.shift = Option.none) {a b : Acc v} (h : Acc.Rel R a b)
    (hf : a.state.fresh = b.state.fresh) (hn : a.state.nextId = b.state.nextId) :
    dataTerm σ' τ' a = dataTerm σ τ b := by
  obtain ⟨⟨hrec, hmach, hpend, hnow, -, -⟩, hev, hout, -, -, hown⟩ := h
  have hp := Multi.sort_map (g := fun p : Pending v.event =>
      Erl.tuple [.int (τ p.id), senderTerm σ p.sender, .bin p.external, requestTerm σ (fun _ => .atom "") p.request])
    (f := fun p : Pending v.event =>
      Erl.tuple [.int (τ' p.id), senderTerm σ' p.sender, .bin p.external, requestTerm σ' (fun _ => .atom "") p.request])
    (fun ⟨_, ps, _, pr⟩ ⟨_, qs, _, qr⟩ ⟨hi, hs, hx, hr⟩ => by
      have hs' : senderTerm σ' ps = senderTerm σ qs := by
        cases hs with
        | machine n hk => simp only [senderTerm, wireTerm_rel hσ h0 hk]
        | reaction n => rfl
      have hr' : requestTerm σ' (fun _ => .atom "") pr = requestTerm σ (fun _ => .atom "") qr := by
        cases hr with
        | mk n i o j hv he _ =>
          cases he <;> simp only [requestTerm, Ty.canonBy_rel hσ h0 _ _ _ hv, Option.toList, List.map]
      rw [hτ hi, hs', hx, hr']) hpend
  have ho := Multi.sort_map
    (f := fun o : OutLine => Erl.tuple [.int (τ' o.id), .bin o.external, .bin o.name, wireTerm σ' o.input])
    (g := fun o : OutLine => Erl.tuple [.int (τ o.id), .bin o.external, .bin o.name, wireTerm σ o.input])
    (fun o o' ⟨hi, hx, hm, hw⟩ => by rw [hτ hi, hx, hm, wireTerm_rel hσ h0 hw]) hout
  have hq := Multi.sort_map (f := ownTerm σ' (fun _ => .atom "")) (g := ownTerm σ (fun _ => .atom ""))
    (fun x y hxy => by
      cases hxy with
      | command n c i j hv _ => simp only [ownTerm, Ty.canonBy_rel hσ h0 _ _ _ hv]
      | query n c i o hv _ => simp only [ownTerm, Ty.canonBy_rel hσ h0 _ _ _ hv]) hown
  simp only [dataTerm, accTerm, Ty.canonBy_rel hσ h0 _ _ _ hrec, machinesTerm_rel hσ h0 _ _ hmach, hp,
    PBij.point_eq h0 hnow, hf, hn, Multi.sort_map (fun x y => Ty.canonBy_rel hσ h0 v.event x y) hev, ho, hq]

/-- A counter renaming that fixes every counter but `f` and `f + 1` agrees with keeping or swapping the two. -/
theorem ctr_choice {R : PBij} (hfix : ∀ n, (n < f ∨ f + 2 ≤ n) → R.rel n n) :
    ∃ ρ, CtrRen f ρ ∧ ∀ {c c'}, R.rel c c' → ρ c = c' := by
  have out : ∀ {c c'}, R.rel c c' → (c < f ∨ f + 2 ≤ c ∨ c' < f ∨ f + 2 ≤ c') → c = c' := by
    intro c c' h hc
    rcases hc with hc | hc | hc | hc
    · exact R.func (hfix c (.inl hc)) h
    · exact R.func (hfix c (.inr hc)) h
    · exact R.inj h (hfix c' (.inl hc))
    · exact R.inj h (hfix c' (.inr hc))
  by_cases hs : R.rel f (f + 1) ∨ R.rel (f + 1) f
  · refine ⟨swapFn f, .inr rfl, fun {c c'} h => ?_⟩
    by_cases hc : c < f ∨ f + 2 ≤ c ∨ c' < f ∨ f + 2 ≤ c'
    · have e := out h hc
      subst e
      unfold swapFn; split <;> (try split) <;> omega
    · rcases hs with hs | hs
      · have : c = f → c' = f + 1 := fun e => R.func (e ▸ h) hs
        have : c' = f + 1 → c = f := fun e => R.inj (e ▸ h) hs
        unfold swapFn; split <;> (try split) <;> omega
      · have : c = f + 1 → c' = f := fun e => R.func (e ▸ h) hs
        have : c' = f → c = f + 1 := fun e => R.inj (e ▸ h) hs
        unfold swapFn; split <;> (try split) <;> omega
  · refine ⟨id, .inl rfl, fun {c c'} h => ?_⟩
    by_cases hc : c < f ∨ f + 2 ≤ c ∨ c' < f ∨ f + 2 ≤ c'
    · exact out h hc
    · show c = c'
      have : ¬ (c = f ∧ c' = f + 1) := fun ⟨e, e'⟩ => hs (.inl (by subst e; subst e'; exact h))
      have : ¬ (c = f + 1 ∧ c' = f) := fun ⟨e, e'⟩ => hs (.inr (by subst e; subst e'; exact h))
      omega

theorem CtrRen.comp {σ ρ : Nat → Nat} (hσ : CtrRen f σ) (hρ : CtrRen f ρ) : CtrRen f (σ ∘ ρ) := by
  rcases hσ with rfl | rfl <;> rcases hρ with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl
  · exact .inl (funext fun a => swapFn_swapFn f a)

theorem wireIds_partner {R : Ren} {a b : Acc v} (h : Acc.Rel R a b) :
    ∀ i ∈ wireIds a, ∃ j ∈ wireIds b, R.wire.rel i j := by
  intro i hi
  simp only [wireIds, List.mem_append, List.mem_map] at hi ⊢
  rcases hi with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩
  · obtain ⟨q, hq, hpq⟩ := Multi.mem_left h.1.2.2.1 hp
    exact ⟨q.id, .inl ⟨q, hq, rfl⟩, hpq.1⟩
  · obtain ⟨o', ho', hoo⟩ := Multi.mem_left h.2.2.1 ho
    exact ⟨o'.id, .inr ⟨o', ho', rfl⟩, hoo.1⟩

theorem covered_of_renamed {a b : Acc v} (h : RenamedFrom f n0 a b) (hf : a.state.fresh = f + 2) :
    DataCovered f n0 a b := by
  obtain ⟨R, h0, hr, hfr, hn, -, hfix, hw⟩ := h
  obtain ⟨ρ, hρ, hρR⟩ := ctr_choice (R := R.ctr) (f := f) fun n hn' => hfix n (hf ▸ hn')
  classical
  let ρw : Nat → Nat := fun i => if h : ∃ j, R.wire.rel i j then h.choose else i
  have hρw : ∀ {i j}, R.wire.rel i j → ρw i = j := fun {i j} h => by
    show (if h : ∃ j, R.wire.rel i j then h.choose else i) = j
    split
    · rename_i he; exact R.wire.func he.choose_spec h
    · rename_i he; exact absurd ⟨j, h⟩ he
  intro σ τ hσ hτ
  refine ⟨σ ∘ ρ, τ ∘ ρw, hσ.comp hρ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi hlt
    obtain ⟨j, hj, hij⟩ := wireIds_partner hr i hi
    have e : i = j := R.wire.func (hw i hlt) hij
    subst e
    show τ (ρw i) = i
    rw [hρw hij]; exact hτ.below i hj hlt
  · intro i hi hle
    obtain ⟨j, hj, hij⟩ := wireIds_partner hr i hi
    have : n0 ≤ j := Nat.le_of_not_lt fun hlt => by
      have := R.wire.inj hij (hw j hlt); omega
    show n0 ≤ τ (ρw i)
    rw [hρw hij]; exact hτ.above j hj this
  · intro i hi i' hi' e
    obtain ⟨j, hj, hij⟩ := wireIds_partner hr i hi
    obtain ⟨j', hj', hij'⟩ := wireIds_partner hr i' hi'
    simp only [Function.comp, hρw hij, hρw hij'] at e
    have := hτ.inj j hj j' hj' e
    subst this
    exact R.wire.inj hij hij'
  · exact (dataTerm_rel (fun {c c'} h => by simp only [Function.comp, hρR h]) (fun {i j} h => by
      simp only [Function.comp, hρw h]) h0 hr hfr hn).symm

/-- `Same` keeps the counter, and from the counter a pair ends at, each side covers the other. -/
theorem covered_of_same {a b : Acc v} (h : Same f n0 a b) :
    a.state.fresh = b.state.fresh ∧ (a.state.fresh = f + 2 → DataCovered f n0 a b ∧ DataCovered f n0 b a) := by
  induction h with
  | @base a b h =>
    have hfr : a.state.fresh = b.state.fresh := by obtain ⟨_, _, _, e, _⟩ := h; exact e
    exact ⟨hfr, fun hf => ⟨covered_of_renamed h hf, covered_of_renamed h.symm (hfr ▸ hf)⟩⟩
  | refl a => exact ⟨rfl, fun _ => ⟨fun σ τ hσ hτ => ⟨σ, τ, hσ, hτ, rfl⟩, fun σ τ hσ hτ => ⟨σ, τ, hσ, hτ, rfl⟩⟩⟩
  | symm _ ih => exact ⟨ih.1.symm, fun hf => (ih.2 (ih.1 ▸ hf)).symm⟩
  | trans _ _ ih1 ih2 =>
    refine ⟨ih1.1.trans ih2.1, fun hf => ?_⟩
    have h1 := ih1.2 hf
    have h2 := ih2.2 (ih1.1 ▸ hf)
    refine ⟨fun σ τ hσ hτ => ?_, fun σ τ hσ hτ => ?_⟩
    · obtain ⟨σ1, τ1, hσ1, hτ1, e1⟩ := h2.1 σ τ hσ hτ
      obtain ⟨σ2, τ2, hσ2, hτ2, e2⟩ := h1.1 σ1 τ1 hσ1 hτ1
      exact ⟨σ2, τ2, hσ2, hτ2, e1.trans e2⟩
    · obtain ⟨σ1, τ1, hσ1, hτ1, e1⟩ := h1.2 σ τ hσ hτ
      obtain ⟨σ2, τ2, hσ2, hτ2, e2⟩ := h2.2 σ1 τ1 hσ1 hτ1
      exact ⟨σ2, τ2, hσ2, hτ2, e1.trans e2⟩

/-- Equal data terms hold the same wire ids once renamed. -/
theorem wireIds_of_data {σ σ' τ τ' : Nat → Nat} {a b : Acc v} (h : dataTerm σ τ a = dataTerm σ' τ' b) :
    ∀ i ∈ wireIds a, ∃ j ∈ wireIds b, τ i = τ' j := by
  simp only [dataTerm, accTerm, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq] at h
  obtain ⟨-, -, hp, -, -, -, -, ho, -⟩ := h
  have hp := (Erl.sort_eq_iff _ _).1 hp
  have ho := (Erl.sort_eq_iff _ _).1 ho
  intro i hi
  simp only [wireIds, List.mem_append, List.mem_map] at hi ⊢
  rcases hi with ⟨p, hpm, rfl⟩ | ⟨o, hom, rfl⟩
  · obtain ⟨q, hq, e⟩ := List.mem_map.1 (hp.mem_iff.1 (List.mem_map_of_mem hpm))
    simp only [Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj] at e
    exact ⟨q.id, .inl ⟨q, hq, rfl⟩, e.1.symm⟩
  · obtain ⟨o', ho', e⟩ := List.mem_map.1 (ho.mem_iff.1 (List.mem_map_of_mem hom))
    simp only [Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj] at e
    exact ⟨o'.id, .inr ⟨o', ho', rfl⟩, e.1.symm⟩

/-- `accTerm` reads the wire renaming only at the ids the step holds. -/
theorem accTerm_congr {σ τ τ' : Nat → Nat} {fn : {t : Ty} → Fun t → Erl} {a : Acc v}
    (h : ∀ i ∈ wireIds a, τ i = τ' i) : accTerm σ τ fn a = accTerm σ τ' fn a := by
  simp only [wireIds, List.mem_append, List.mem_map] at h
  have hp : a.state.pending.map (fun p => Erl.tuple [.int (τ p.id), senderTerm σ p.sender, .bin p.external,
      requestTerm σ fn p.request]) = a.state.pending.map fun p => Erl.tuple [.int (τ' p.id), senderTerm σ p.sender,
      .bin p.external, requestTerm σ fn p.request] :=
    List.map_congr_left fun p hp => by rw [h p.id (.inl ⟨p, hp, rfl⟩)]
  have ho : a.out.map (fun o => Erl.tuple [.int (τ o.id), .bin o.external, .bin o.name, wireTerm σ o.input]) =
      a.out.map fun o => Erl.tuple [.int (τ' o.id), .bin o.external, .bin o.name, wireTerm σ o.input] :=
    List.map_congr_left fun o ho => by rw [h o.id (.inr ⟨o, ho, rfl⟩)]
  simp only [accTerm, hp, ho]

theorem injections_complete (τ : Nat → Nat) : (is avail : List Nat) → (∀ i ∈ is, ∀ j ∈ is, τ i = τ j → i = j) →
    (∀ i ∈ is, τ i ∈ avail) → ∃ m ∈ injections is avail, ∀ i, assignWire m i = if i ∈ is then τ i else i
  | [], _, _, _ => ⟨[], by simp [injections], fun i => by simp [assignWire]⟩
  | i :: is, avail, hinj, hin => by
    by_cases h : i ∈ is
    · obtain ⟨m, hm, ha⟩ := injections_complete τ is avail (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))
        (fun a ha => hin a (by simp [ha]))
      refine ⟨m, by simp only [injections, h, ↓reduceIte]; exact hm, fun a => ?_⟩
      rw [ha a]
      by_cases e : a = i
      · subst e; simp [h]
      · simp [e]
    · have hne : ∀ a ∈ is, τ a ≠ τ i := fun a ha e => h (hinj a (by simp [ha]) i (by simp) e ▸ ha)
      obtain ⟨m, hm, ha⟩ := injections_complete τ is (avail.erase (τ i))
        (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))
        (fun a ha => (List.mem_erase_of_ne (hne a ha)).2 (hin a (by simp [ha])))
      refine ⟨(i, τ i) :: m, ?_, fun a => ?_⟩
      · simp only [injections, h, ↓reduceIte, List.mem_flatMap, List.mem_map]
        exact ⟨τ i, hin i (by simp), m, hm, rfl⟩
      · by_cases e : a = i
        · subst e; simp [assignWire, List.lookup]
        · have hb : (a == i) = false := by simp [e]
          have := ha a
          simp only [assignWire, List.lookup, hb, List.mem_cons, e, false_or] at this ⊢
          exact this

/-- Steps in progress that `Same` relates, from the counter a pair ends at, meet in `dataTerm` under a renaming
`pairRenamings` lists. -/
theorem data_of_same {A C : Acc v} (h : Same f n0 A C) (hf : A.state.fresh = f + 2) :
    ∃ r ∈ pairRenamings f n0 A C, dataTerm r.1 r.2 C = dataTerm id id A := by
  obtain ⟨σ, τ, hσ, hτ, e⟩ := ((covered_of_same h).2 hf).2 id id (.inl rfl)
    ⟨fun _ _ _ => rfl, fun _ _ h => h, fun _ _ _ _ h => h⟩
  have himg : ∀ i ∈ newIds n0 C, τ i ∈ (newIds n0 A).eraseDups := by
    intro i hi
    simp only [newIds, List.mem_filter, decide_eq_true_eq] at hi
    obtain ⟨j, hj, hij⟩ := wireIds_of_data e.symm i hi.1
    rw [List.mem_eraseDups]
    simp only [newIds, List.mem_filter, decide_eq_true_eq, hij]
    exact ⟨hj, hij ▸ hτ.above i hi.1 hi.2⟩
  obtain ⟨m, hm, ha⟩ := injections_complete τ (newIds n0 C) _
    (fun i hi j hj => hτ.inj i (List.mem_filter.1 hi).1 j (List.mem_filter.1 hj).1) himg
  refine ⟨(σ, assignWire m), ?_, ?_⟩
  · simp only [pairRenamings, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨σ, hσ, m, hm, rfl⟩
  · refine (accTerm_congr fun i hi => ?_).trans e.symm
    show assignWire m i = τ i
    rw [ha i]
    by_cases hn : n0 ≤ i
    · simp [newIds, hi, hn]
    · have : i ∉ newIds n0 C := by simp [newIds, hn]
      simp only [this, ↓reduceIte]; exact (hτ.below i hi (by omega)).symm

end Complete

/-- A pair whose orders show a disabling, a fault in one order only, or different data under every renaming searched
does not commute. -/
theorem pair_violates (T : List TypeDecl) {a0 : Step.Acc v} {e1 e2 : OwnEffectV v.event} {r : PairOrders}
    (h : pairOrders T a0 e1 e2 = .ok r) (hr : r.violated = true) :
    ¬ Step.PairCommutes T a0 e1 e2 := by
  intro hc
  unfold pairOrders at h
  cases h1 : Step.runOwn T a0 e1 with
  | error _ => rw [h1] at h; cases h
  | ok b =>
    rw [h1] at h
    obtain ⟨hc1, hc2⟩ := hc b h1
    cases h2 : Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) e2 <;>
      cases h3 : Step.runOwn T b e2 <;> cases h4 : Step.canonPair T a0 e1 e2 <;>
      simp only [h2, h3, h4] at h hc1 hc2
    all_goals first
      | exact (hc2 _ rfl).elim
      | exact (hc1 _ rfl).elim (fun h => h.elim) fun h => h.2.elim
      | exact (hc1 _ rfl).elim (fun h => h.elim) fun h => h.1.elim
      | cases h; done
      | skip
    rename_i c A C
    have hs : Same a0.state.fresh a0.state.nextId A C :=
      (hc1 c rfl).elim id fun h => h.1.elim
    have hf : A.state.fresh = a0.state.fresh + 2 := by
      rw [runOwn_fresh T h3, runOwn_fresh T h1]
    obtain ⟨⟨σ, τ⟩, hm, e⟩ := data_of_same hs hf
    cases h
    cases hsu : sameUpToPair a0.state.fresh a0.state.nextId A C <;>
      simp only [hsu, PairOrders.violated, Bool.false_eq_true] at hr
    have hd : ((pairRenamings a0.state.fresh a0.state.nextId A C).any fun r =>
        dataTerm r.1 r.2 C == dataTerm id id A) = true :=
      List.any_eq_true.2 ⟨(σ, τ), hm, beq_iff_eq.2 e⟩
    simp only [sameUpToPair, hd, ↓reduceIte] at hsu
    split at hsu <;> (try split at hsu) <;> cases hsu

end Tazuna.Smt
