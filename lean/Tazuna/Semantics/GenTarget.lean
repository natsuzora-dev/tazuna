import Tazuna.Semantics.PendingInv
import Tazuna.Semantics.Start

/-! What `generate` aims at. verify judges an implementation by its out lines, so a test input is worth writing when
it makes the service show a class of out line: an answer's outcome to a command or query, an event by its variant, a
request to an external's command or query (`OutClass`). Machine states show in no out line, so they are no targets.
The targets are enumerated from the spec's declarations (`targets`); `classes_covered` says the enumeration misses
no class a step can show. Rule names are the one part a spec can compute: a rule whose name is no literal is aimed at
as "a rule of a computed name" (`GenTarget.invalid _ none`), and the literal names are read off the checked IR's
`accepts` sources (`ruleNamesOf`), so every target exists whether or not a step's encoding is refused
(`targets_cover`). -/

namespace Tazuna.Ir

open Step

section Variants
variable (T : List TypeDecl)

/-- Which constructor built a value of a custom type, counted from 0. -/
def altIndex : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Nat
  | [], x => nomatch x
  | _ :: _, .inl _ => 0
  | _ :: vs, .inr y => altIndex vs y + 1

theorem altIndex_lt : (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) → altIndex vs x < vs.length
  | [], x => nomatch x
  | _ :: _, .inl _ => by simp [altIndex]
  | _ :: vs, .inr y => by simpa [altIndex] using altIndex_lt vs y

/-- The name of constructor `k` of the type the table declares at `i`; none where the table has none. -/
def variantName (i k : Nat) : Option String := ((T[i]?).bind (·.variants[k]?)).map (·.name)

/-- The constructor a value of a custom type is built with, by name; none for other types. -/
def variantOf : (t : Ty) → t.den0 → Option String
  | .adt i _ vs, x => variantName T i (altIndex vs x)
  | _, _ => none

/-- Every constructor name `variantOf` can give at the type. -/
def variantsOf : Ty → List (Option String)
  | .adt i _ vs => (List.range vs.length).map (variantName T i)
  | _ => [none]

theorem variantOf_mem : (t : Ty) → (x : t.den0) → variantOf T t x ∈ variantsOf T t
  | .adt _ _ vs, x => List.mem_map.2 ⟨altIndex vs x, List.mem_range.2 (altIndex_lt vs x), rfl⟩
  | .int, _ | .str, _ | .list _, _ | .tuple _, _ | .fn _ _, _ | .param _, _ | .bag _, _ | .table _ _, _
  | .date, _ | .id, _ | .dsl _ _, _ => List.mem_singleton.2 rfl

end Variants

/-- One class of out line, as a log shows it. -/
inductive OutClass where
  /-- The answer `accepted` to the command. -/
  | accepted (command : String)
  /-- The answer `rejected` to the command, with the constructor of its rejection. -/
  | rejected (command : String) (variant : Option String)
  /-- The answer `invalid` to the command or query, naming the rule. -/
  | invalid (request : String) (rule : String)
  /-- The answer `answered` to the query. -/
  | answered (query : String)
  /-- An event the service applied, by its constructor. -/
  | event (variant : Option String)
  /-- A request the service sent to the external's command or query. -/
  | request (external name : String)
deriving DecidableEq, Repr

/-- What generate aims at: one class of out line, except that `invalid` names a literal rule or, with none, any rule
whose name is no literal. -/
inductive GenTarget where
  | accepted (command : String)
  | rejected (command : String) (variant : Option String)
  | invalid (request : String) (rule : Option String)
  | answered (query : String)
  | event (variant : Option String)
  | request (external name : String)
deriving DecidableEq, Repr

/-- The rule names a command's or query's answers can name, by its name: each literal, and none where some rule's
name is computed. Admission's own rule `callers` is always one. -/
abbrev RuleNames := String → List (Option String)

/-- The literal rule names of a command or query. -/
def RuleNames.literals (rules : RuleNames) (request : String) : List String := "callers" :: (rules request).filterMap id

/-- Whether the target aims at the class. -/
def GenTarget.covers (rules : RuleNames) : GenTarget → OutClass → Bool
  | .accepted c, .accepted c' => c == c'
  | .rejected c k, .rejected c' k' => c == c' && k == k'
  | .invalid q (some r), .invalid q' r' => q == q' && r == r'
  | .invalid q none, .invalid q' r' => q == q' && !(rules.literals q).contains r'
  | .answered q, .answered q' => q == q'
  | .event k, .event k' => k == k'
  | .request x n, .request x' n' => x == x' && n == n'
  | _, _ => false

section
variable (T : List TypeDecl) (v : ServiceV)

/-- The class of the answer to a command or query with the outcome; none for a fault, which a log never shows, nor
for other inputs, which get no answer line. -/
def answerClasses : Input v → Outcome → List OutClass
  | .command i .., .accepted => [.accepted (v.commands.get i).name]
  | .command i .., .rejected w => [.rejected (v.commands.get i).name (variantOf T w.1 w.2)]
  | .command i .., .invalid rs => rs.map (.invalid (v.commands.get i).name)
  | .query i .., .answered _ => [.answered (v.queries.get i).name]
  | .query i .., .invalid rs => rs.map (.invalid (v.queries.get i).name)
  | _, _ => []

/-- The classes of out line a step's result `r` on the input `x` shows: the answer, each event applied, each request
sent. -/
def classes (x : Input v) (r : Result v) : List OutClass :=
  answerClasses T v x r.outcome ++ r.events.map (fun ev => .event (variantOf T v.event ev)) ++
    r.out.map fun o => .request o.external o.name

/-- The invalid targets of a command or query: admission's `callers`, then each rule name. -/
def invalidTargets (rules : RuleNames) (request : String) : List GenTarget :=
  (some "callers" :: rules request).map (.invalid request)

/-- Every target of the service, in a fixed order: per command its accepted, rejected per constructor and invalid
targets; per query its answered and invalid targets; an event per constructor; a request per external command or
query some sender can send (`shapes`), once however many senders can. -/
def targets (rules : RuleNames) : List GenTarget :=
  (v.commands.flatMap fun x => .accepted x.name :: (variantsOf T x.rejection).map (.rejected x.name) ++
    invalidTargets rules x.name) ++
  (v.queries.flatMap fun q => .answered q.name :: invalidTargets rules q.name) ++
  (variantsOf T v.event).map .event ++
  dedupBy (· == ·) ((shapes v).map fun sh => .request sh.external sh.name)

end

/-- Every rule an admission can name is a literal of `rules` or `rules` has a computed name: what the reader of the
literal names must give. -/
def RulesListed (v : ServiceV) (rules : RuleNames) : Prop :=
  (∀ i : Fin v.commands.length, ∀ input, ∀ n ∈ broken ((v.commands.get i).accepts.fn (input, ())),
    some n ∈ rules (v.commands.get i).name ∨ none ∈ rules (v.commands.get i).name) ∧
  (∀ i : Fin v.queries.length, ∀ input, ∀ n ∈ broken ((v.queries.get i).accepts.fn (input, ())),
    some n ∈ rules (v.queries.get i).name ∨ none ∈ rules (v.queries.get i).name)

section
variable {G : List Ty}

/-- A string literal's text. -/
def Expr.strLit? {Γ : List Ty} {t : Ty} : Expr G Γ t → Option String
  | .str s => some s.1
  | _ => none

/-- The first expression's text where it is a string literal. -/
def Exprs.headStr? {Γ : List Ty} {ts : List Ty} : Exprs G Γ ts → Option String
  | .cons e _ => e.strLit?
  | .nil => none

/-- A rule's name as written: the literal of a rule written as the tuple `#("name", cond)`. -/
def Expr.ruleName? {Γ : List Ty} {t : Ty} : Expr G Γ t → Option String
  | .tuple es => es.headStr?
  | _ => none

/-- The names of a list literal's rules: each one's literal, or none. -/
def Items.ruleNames {Γ : List Ty} {t : Ty} : Items G Γ t → List (Option String)
  | .nil => []
  | .cons e es => e.ruleName? :: es.ruleNames

/-- The names of the rules a list expression gives: its items' where it is a list literal, else one computed name. -/
def Expr.ruleNames {Γ : List Ty} {t : Ty} : Expr G Γ t → List (Option String)
  | .list items => items.ruleNames
  | _ => [none]

/-- The names of the rules a function gives, read off its body where it is a lambda, else one computed name. -/
def Expr.lamRuleNames {Γ : List Ty} {t : Ty} : Expr G Γ t → List (Option String)
  | .lam body => body.ruleNames
  | _ => [none]

variable (D : Defs G) (g : Ty.dens G)

theorem Expr.ruleName?_eval {Γ : List Ty} : {t : Ty} → (e : Expr G Γ t) → (h : t = .tuple [.str, .bool]) →
    (s : String) → e.ruleName? = some s → (ρ : Ty.dens Γ) →
      (show Str from (h ▸ e.eval D g ρ : (Ty.tuple [.str, .bool]).den).1).1 = s := by
  intro t e h s hs ρ
  cases e with
  | tuple es =>
    cases es with
    | nil => cases hs
    | cons e1 rest =>
      cases e1 with
      | str s' =>
        simp only [Expr.ruleName?, Exprs.headStr?, Expr.strLit?, Option.some.injEq] at hs
        subst hs
        injection h with h1
        injection h1 with _ h2
        subst h2
        rfl
      | _ => cases hs
  | _ => cases hs

theorem Items.ruleNames_mem {Γ : List Ty} (ρ : Ty.dens Γ) (items : Items G Γ (.tuple [.str, .bool])) :
    ∀ a ∈ Items.eval D g items ρ, some (show Str from a.1).1 ∈ items.ruleNames ∨ none ∈ items.ruleNames := by
  generalize hl : Items.eval D g items ρ = xs
  induction xs generalizing items with
  | nil => simp
  | cons x xs ih =>
    cases items with
    | nil => simp [Items.eval] at hl
    | cons e es =>
      simp only [Items.eval, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · cases hr : e.ruleName? with
        | none => simp [Items.ruleNames, hr]
        | some s =>
          have := Expr.ruleName?_eval D g e rfl s hr ρ
          simp only [Items.ruleNames, hr, ← this]
          exact Or.inl List.mem_cons_self
      · rcases ih es hl a ha with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem Expr.ruleNames_listed {Γ : List Ty} (ρ : Ty.dens Γ) : {t : Ty} → (e : Expr G Γ t) → (h : t = Ty.rules) →
    ∀ n ∈ broken (h ▸ e.eval D g ρ : Ty.rules.den), some n ∈ e.ruleNames ∨ none ∈ e.ruleNames := by
  intro t e h n hn
  cases e with
  | list items =>
    injection h with h1
    subst h1
    obtain ⟨⟨m, b, ⟨⟩⟩, ha, hf⟩ := List.mem_filterMap.1 hn
    have hm : (show Str from m).1 = n := by
      simp only at hf
      split at hf
      · cases hf
      · cases hf; rfl
    subst hm
    exact Items.ruleNames_mem D g ρ items _ ha
  | _ => exact Or.inr (by simp [Expr.ruleNames])

theorem Expr.lamRuleNames_listed {Γ : List Ty} {i : Ty} (ρ : Ty.dens Γ) : {t : Ty} → (e : Expr G Γ t) →
    (h : t = .fn [i] Ty.rules) → ∀ ys, ∀ n ∈ broken ((h ▸ e.eval D g ρ : (Ty.fn [i] Ty.rules).den) ys : Ty.rules.den),
      some n ∈ e.lamRuleNames ∨ none ∈ e.lamRuleNames := by
  intro t e h ys n hn
  cases e with
  | lam body =>
    injection h with h1 h2
    subst h1; subst h2
    exact Expr.ruleNames_listed D g _ body rfl n hn
  | _ => exact Or.inr (by simp [Expr.lamRuleNames])

end

/-- The names of the rules a kept `accepts` function gives, read off its source as `Step.broken` reads them. -/
def Fun.ruleNames {t : Ty} (f : Fun t) : List (Option String) := f.body.lamRuleNames

theorem Fun.fn_app {ps : List Ty} {r : Ty} (f : Fun (.fn ps r)) (hps : (Ty.tuple ps).isData = true)
    (hr : r.isData = true) (xs : (Ty.tuple ps).den0) : f.fn xs = Ty.down r hr (f.eval (Ty.up (.tuple ps) hps xs)) := by
  have := Ty.up_fn ps r f.ht hps hr f.fn xs
  rw [Fun.fn, Ty.up_down] at this
  rw [this, Ty.down_up]
  rfl

/-- Every rule an `accepts` function breaks is named by a literal its source writes, or the source computes a name. -/
theorem Fun.ruleNames_listed {i : Ty} (f : Fun (.fn [i] Ty.rules)) (x : i.den0) :
    ∀ n ∈ broken (f.fn (x, ())), some n ∈ f.ruleNames ∨ none ∈ f.ruleNames := by
  have hps : (Ty.tuple [i]).isData = true := by
    have := f.ht; simp only [Ty.isData, Bool.and_eq_true] at this; simpa [Ty.isData] using this.1
  intro n hn
  have e := Fun.fn_app f hps rfl (x, ())
  erw [e] at hn
  exact Expr.lamRuleNames_listed f.defs f.defs.eval _ f.body rfl _ n hn

/-- The rule names of each command and query, read off the checked IR's `accepts` (`Fun.ruleNames`), so they exist
whether or not a step's encoding is refused. -/
def ruleNamesOf (v : ServiceV) : RuleNames := fun name =>
  dedupBy (· == ·) ((v.commands.filter (·.name == name)).flatMap (·.accepts.ruleNames) ++
    (v.queries.filter (·.name == name)).flatMap (·.accepts.ruleNames))

theorem rulesListed_ofIr (v : ServiceV) : RulesListed v (ruleNamesOf v) := by
  have mem : ∀ {name : String} {o : Option String} {fs : List (List (Option String))},
      (∃ l ∈ fs, o ∈ l) → (fs.flatten ⊆ (ruleNamesOf v name)) → o ∈ ruleNamesOf v name :=
    fun ⟨l, hl, ho⟩ hs => hs (List.mem_flatten.2 ⟨l, hl, ho⟩)
  refine ⟨fun i input n hn => ?_, fun i input n hn => ?_⟩
  · have hin : ∀ o ∈ (v.commands.get i).accepts.ruleNames, o ∈ ruleNamesOf v (v.commands.get i).name := fun o ho =>
      (mem_dedupBy (fun _ _ => beq_iff_eq) _ _).2 (List.mem_append_left _
        (List.mem_flatMap.2 ⟨_, List.mem_filter.2 ⟨List.get_mem _ i, by simp⟩, ho⟩))
    rcases Fun.ruleNames_listed _ input n hn with h | h
    · exact .inl (hin _ h)
    · exact .inr (hin _ h)
  · have hin : ∀ o ∈ (v.queries.get i).accepts.ruleNames, o ∈ ruleNamesOf v (v.queries.get i).name := fun o ho =>
      (mem_dedupBy (fun _ _ => beq_iff_eq) _ _).2 (List.mem_append_right _
        (List.mem_flatMap.2 ⟨_, List.mem_filter.2 ⟨List.get_mem _ i, by simp⟩, ho⟩))
    rcases Fun.ruleNames_listed _ input n hn with h | h
    · exact .inl (hin _ h)
    · exact .inr (hin _ h)

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- What a step in progress sent: the requests it added to the pending table after `base`, in order, are its out
lines. -/
def Sent (base : List (Pending v.event)) (a : Acc v) : Prop :=
  ∃ ps, a.state.pending = base ++ ps ∧ a.out = ps.map Pending.line

theorem start_sent {base : List (Pending v.event)} : (effs : List (Sender × EffectV v.event)) → (a : Acc v) →
    Sent base a → ∀ b, start a effs = .ok b → Sent base b
  | [], a, h, b, hs => by
    simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ h
  | (snd, eff) :: effs, a, h, b, hs => by
    simp only [start, List.foldlM_cons] at hs
    cases eff with
    | request r =>
      cases ho : r.ownerIn v.declared with
      | none => simp only [ho] at hs; cases hs
      | some x =>
        simp only [ho, bind, Except.bind] at hs
        refine start_sent effs _ ?_ b hs
        obtain ⟨ps, hp, hout⟩ := h
        exact ⟨ps ++ [⟨a.state.nextId, snd, x, r⟩], by simp [hp], by simp [hout, Pending.line]⟩
    | command => simp only [bind, Except.bind] at hs; refine start_sent effs _ ?_ b hs; exact h
    | query => simp only [bind, Except.bind] at hs; refine start_sent effs _ ?_ b hs; exact h

theorem applyEvents_sent {base : List (Pending v.event)} : (evs : List v.event.den0) → (a : Acc v) → Sent base a →
    ∀ b, applyEvents T a evs = .ok b → Sent base b
  | [], a, h, b, hs => by
    simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ h
  | ev :: evs, a, h, b, hs => by
    unfold applyEvents at hs
    rw [List.foldlM_cons] at hs
    cases h1 : start { a with state := (react T a.state ev).1, events := a.events ++ [ev] } (react T a.state ev).2 with
    | error e => simp [h1, bind, Except.bind] at hs
    | ok a1 =>
      simp only [h1, bind, Except.bind] at hs
      refine applyEvents_sent evs a1 (start_sent _ _ ?_ a1 h1) b hs
      exact h

theorem execCommand_sent {base : List (Pending v.event)} (a : Acc v) (x : CommandV v.records v.event v.caller)
    (c : (Ty.origin v.caller).den0) (i : x.input.den0) (h : Sent base a) :
    (∀ b, execCommand T a x c i = .ok (.accepted b) → Sent base b) ∧
    (∀ b j, execCommand T a x c i = .ok (.rejected b j) → Sent base b) := by
  have ha : Sent base ({ a with state := { a.state with fresh := a.state.fresh + 1 } } : Acc v) := h
  unfold execCommand
  cases had : admit x.callers x.accepts c i with
  | cons r rs => exact ⟨fun _ hb => by simp at hb, fun _ _ hb => by simp at hb⟩
  | nil =>
    simp only
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = d
    match d with
    | .inl (evs, ()) =>
      simp only [bind, Except.bind]
      cases h3 : applyEvents T { a with state := { a.state with fresh := a.state.fresh + 1 } } evs with
      | error e => exact ⟨fun _ hb => by simp at hb, fun _ _ hb => by simp at hb⟩
      | ok a3 =>
        cases hen : broken (x.ensures.fn (ctx a.state a.state.records c i, a3.state.records, ())) with
        | cons n ns => exact ⟨fun _ hb => by simp [hen] at hb, fun _ _ hb => by simp [hen] at hb⟩
        | nil =>
          refine ⟨fun b hb => ?_, fun b j hb => by simp [hen] at hb⟩
          simp only [hen, Except.ok.injEq, Ran.accepted.injEq] at hb
          exact hb ▸ applyEvents_sent T _ _ ha _ h3
    | .inr (.inl (j, ())) => exact ⟨fun _ hb => (by cases hb), fun b j hb => (by cases hb; exact ha)⟩

theorem runCommand_sent {base : List (Pending v.event)} {a b : Acc v} {x : CommandV v.records v.event v.caller}
    {c : (Ty.origin v.caller).den0} {i : x.input.den0} {f : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))}
    (h : Sent base a) (hb : runCommand T a x c i f = .ok b) : Sent base b := by
  unfold runCommand at hb
  simp only [bind, Except.bind] at hb
  split at hb
  · cases hb
  · rename_i r hr
    cases r with
    | invalid => cases hb
    | accepted a1 => exact applyEvents_sent T _ _ ((execCommand_sent T a _ _ _ h).1 a1 hr) b hb
    | rejected a1 j => exact applyEvents_sent T _ _ ((execCommand_sent T a _ _ _ h).2 a1 j hr) b hb

theorem runOwn_sent {base : List (Pending v.event)} (a : Acc v) (e : OwnEffectV v.event) (h : Sent base a) :
    ∀ b, runOwn T a e = .ok b → Sent base b := by
  intro b hb
  cases e with
  | command name c i j value onAnswer =>
    dsimp only [runOwn] at hb
    revert hb
    generalize Ty.same c v.caller = oc
    generalize ownCommand (v := v) name i j = ox
    cases oc with
    | none => intro hb; change Except.error _ = _ at hb; cases hb
    | some hcp =>
      cases ox with
      | none => intro hb; change Except.error _ = _ at hb; cases hb
      | some x =>
        obtain ⟨hcp⟩ := hcp
        obtain ⟨x, hi, hj⟩ := x
        subst hcp hi hj
        intro hb
        change runCommand T a x _ _ _ = _ at hb
        exact runCommand_sent T h hb
  | query name c i o value onAnswer =>
    dsimp only [runOwn] at hb
    revert hb
    generalize Ty.same c v.caller = oc
    generalize ownQuery (v := v) name i o = ox
    cases oc with
    | none => intro hb; change Except.error _ = _ at hb; cases hb
    | some hcp =>
      cases ox with
      | none => intro hb; change Except.error _ = _ at hb; cases hb
      | some x =>
        obtain ⟨hcp⟩ := hcp
        obtain ⟨x, hi, ho⟩ := x
        subst hcp hi ho
        intro hb
        change runQuery T a x _ _ _ = _ at hb
        unfold runQuery at hb
        split at hb
        · cases hb
        · refine applyEvents_sent T _ _ ?_ b hb
          exact h

theorem settle_sent {base : List (Pending v.event)} : (fuel : Nat) → (a : Acc v) → Sent base a →
    ∀ b, settle T fuel a = .ok b → Sent base b
  | fuel, a, h, b, hb => by
    unfold settle at hb
    match hown : a.own, fuel, hb with
    | [], _, hb => cases hb; exact h
    | _ :: _, 0, hb => cases hb
    | e :: rest, f + 1, hb =>
      simp only [bind, Except.bind] at hb
      split at hb
      · cases hb
      · rename_i a1 h1
        refine settle_sent f a1 (runOwn_sent T _ e ?_ a1 h1) b hb
        exact h

theorem finish_sent (s0 : State v) (r : Except Fault (Acc v)) (o : Outcome) {base : List (Pending v.event)}
    (h0 : base.Sublist s0.pending) (hr : ∀ a, r = .ok a → Sent base a) :
    ∃ base' ps, base'.Sublist s0.pending ∧ (finish T s0 r o).state.pending = base' ++ ps ∧
      (finish T s0 r o).out = ps.map Pending.line := by
  unfold finish
  split
  · exact ⟨_, [], .refl _, by simp, rfl⟩
  · rename_i a h
    split
    · exact ⟨_, [], .refl _, by simp, rfl⟩
    · cases r with
      | error => simp [bind, Except.bind] at h
      | ok a0 =>
        simp only [bind, Except.bind] at h
        obtain ⟨ps, h1, h2⟩ := settle_sent T _ a0 (hr a0 rfl) a h
        exact ⟨base, ps, h0, h1, h2⟩

theorem fire_pending : (fuel : Nat) → (s : State v) → ∀ s' effs, fire s fuel = some (s', effs) → s'.pending = s.pending
  | 0, _, _, _, h => by simp [fire] at h
  | fuel + 1, s, s', effs, h => by
    unfold fire at h
    split at h
    · cases h; rfl
    · obtain ⟨p, h1, he⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨s1, e1⟩ := p
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := fire_pending fuel _ s1 e1 h1
      exact this

/-- A step keeps some of the requests that waited, in order, and adds the ones it sends: its out lines. -/
theorem step_sent (s : State v) (x : Input v) :
    ∃ base ps, base.Sublist s.pending ∧ (step T v s x).state.pending = base ++ ps ∧
      (step T v s x).out = ps.map Pending.line := by
  have h0 : ∀ s' : State v, Sent s'.pending ({ state := s' } : Acc v) := fun s' => ⟨[], by simp, rfl⟩
  cases x with
  | command i caller input =>
    simp only [step]
    split
    · exact ⟨_, [], .refl _, by simp, rfl⟩
    · exact ⟨_, [], .refl _, by simp, rfl⟩
    · exact ⟨_, [], .refl _, by simp, rfl⟩
    · rename_i a ha
      exact finish_sent T { s with fresh := s.fresh + 1 } _ _ (base := s.pending) (.refl _) fun b hb => by
        obtain rfl := Except.ok.inj hb; exact (execCommand_sent T _ _ _ _ (h0 s)).1 a ha
  | query i caller input =>
    simp only [step]
    split <;> exact ⟨_, [], .refl _, by simp, rfl⟩
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step]
    split
    · exact ⟨_, [], .refl _, by simp, rfl⟩
    · split
      · exact ⟨_, [], .refl _, by simp, rfl⟩
      · split
        · exact ⟨_, [], .refl _, by simp, rfl⟩
        · exact finish_sent T s _ .accepted List.filter_sublist fun b hb => applyEvents_sent T _ _ (h0 _) b hb
  | event i value =>
    exact finish_sent T s _ .accepted (.refl _) fun b hb => applyEvents_sent T _ _ (h0 _) b hb
  | clock time =>
    simp only [step]
    split
    · exact ⟨_, [], .refl _, by simp, rfl⟩
    · split
      · exact ⟨_, [], .refl _, by simp, rfl⟩
      · rename_i s' effs hf
        exact finish_sent T s _ .accepted (base := s.pending) (.refl _) fun b hb =>
          start_sent _ _ (by have := h0 s'; rwa [fire_pending _ _ s' effs hf] at this) b hb

/-- Every out line of a step is the line of a request that waits after it. -/
theorem step_outsWait (s : State v) (x : Input v) :
    ∀ l ∈ (step T v s x).out, ∃ p ∈ (step T v s x).state.pending, l = p.line := by
  obtain ⟨_base, ps, _, hp, ho⟩ := step_sent T s x
  intro l hl
  rw [ho] at hl
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hl
  exact ⟨p, hp ▸ List.mem_append_right _ hpm, rfl⟩

end Step

theorem pendingOf_shape {e : Ty} : (shs : List (PendingShape e)) → (id : Nat) →
    (x : Ty.alts (shs.map PendingShape.fields)) →
    ∃ sh ∈ shs, sh.external = (pendingOf shs id x).external ∧ sh.name = (pendingOf shs id x).request.name
  | sh :: _, _, .inl _ => ⟨sh, List.mem_cons_self, rfl, rfl⟩
  | _ :: shs, id, .inr y => by
    obtain ⟨sh, hm, h⟩ := pendingOf_shape shs id y
    exact ⟨sh, List.mem_cons_of_mem _ hm, h⟩

section
variable {T : List TypeDecl} {v : ServiceV}

theorem mem_admit {i : Ty} {callers : List (Ty.origin v.caller).den0} {accepts : Fun (Ty.fn [i] Ty.rules)} {caller : (Ty.origin v.caller).den0}
    {input : i.den0} {n : String} (h : n ∈ admit callers accepts caller input) :
    n = "callers" ∨ n ∈ broken (accepts.fn (input, ())) := by
  unfold admit at h
  split at h
  · exact .inr h
  · exact .inl (List.mem_singleton.1 h)

theorem finish_outcome (s0 : State v) (r : Except Fault (Acc v)) (o : Outcome) :
    (finish T s0 r o).outcome = o ∨ ∃ f, (finish T s0 r o).outcome = .fault f := by
  unfold finish
  split
  · exact .inr ⟨_, rfl⟩
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl

/-- A command's answer: Invalid with admission's rules, or rejected with a value of its rejection type, or accepted,
or a fault. -/
theorem execCommand_invalid {a : Acc v} {x : CommandV v.records v.event v.caller} {c : (Ty.origin v.caller).den0}
    {i : x.input.den0} {rs : List String} (h : execCommand T a x c i = .ok (.invalid rs)) :
    rs = admit x.callers x.accepts c i := by
  unfold execCommand at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs' => simp only [had, Except.ok.injEq, Ran.invalid.injEq] at h; exact h.symm
  | nil =>
    simp only [had] at h
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = d at h
    match d with
    | .inl (evs, ()) =>
      simp only [bind, Except.bind] at h
      cases h3 : applyEvents T { a with state := { a.state with fresh := a.state.fresh + 1 } } evs with
      | error e => simp [h3] at h
      | ok a3 => simp only [h3] at h; split at h <;> cases h
    | .inr (.inl (j, ())) => cases h

theorem step_command_outcome (s : State v) (i : Fin v.commands.length) (caller : v.caller.den0)
    (input : (v.commands.get i).input.den0) :
    (∀ rs, (step T v s (.command i caller input)).outcome = .invalid rs →
      rs = admit (v.commands.get i).callers (v.commands.get i).accepts (outside caller) input) ∧
    (∀ w, (step T v s (.command i caller input)).outcome = .rejected w → w.1 = (v.commands.get i).rejection) := by
  simp only [step]
  split
  · rename_i rs h
    refine ⟨fun _ h' => ?_, fun _ h' => nomatch h'⟩
    cases h'
    exact execCommand_invalid h
  · refine ⟨fun _ h => (nomatch h), fun _ h => ?_⟩
    cases h; rfl
  · exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  · rename_i a _
    rcases finish_outcome (T := T) { s with fresh := s.fresh + 1 } (.ok a) .accepted with h | ⟨f, h⟩
    · refine ⟨fun _ h' => ?_, fun _ h' => ?_⟩ <;> (rw [h] at h'; cases h')
    · refine ⟨fun _ h' => ?_, fun _ h' => ?_⟩ <;> (rw [h] at h'; cases h')

/-- A query's answer: Invalid with admission's rules, or answered. -/
theorem step_query_outcome (s : State v) (i : Fin v.queries.length) (caller : v.caller.den0)
    (input : (v.queries.get i).input.den0) (rs : List String)
    (h : (step T v s (.query i caller input)).outcome = .invalid rs) :
    rs = admit (v.queries.get i).callers (v.queries.get i).accepts (outside caller) input := by
  simp only [step] at h
  split at h
  · rename_i rs' he
    cases h
    unfold execQuery at he
    split at he
    · cases he; rename_i had; exact had.symm
    · cases he
  · cases h

end

theorem invalid_covered {rules : RuleNames} {name : String} {n : String}
    (hn : n = "callers" ∨ some n ∈ rules name ∨ none ∈ rules name) :
    ∃ g ∈ invalidTargets rules name, g.covers rules (.invalid name n) = true := by
  by_cases hl : n ∈ rules.literals name
  · refine ⟨.invalid name (some n), ?_, by simp [GenTarget.covers]⟩
    rcases List.mem_cons.1 hl with rfl | hl
    · exact List.mem_map.2 ⟨some "callers", List.mem_cons_self, rfl⟩
    · obtain ⟨o, ho, he⟩ := List.mem_filterMap.1 hl
      cases he
      exact List.mem_map.2 ⟨_, List.mem_cons_of_mem _ ho, rfl⟩
  · have hnone : none ∈ rules name := by
      rcases hn with rfl | hs | hn
      · exact absurd List.mem_cons_self hl
      · exact absurd (List.mem_cons_of_mem _ ((List.mem_filterMap (f := id)).2 ⟨some n, hs, rfl⟩)) hl
      · exact hn
    refine ⟨.invalid name none, List.mem_map.2 ⟨none, List.mem_cons_of_mem _ hnone, rfl⟩, ?_⟩
    simp [GenTarget.covers, hl]

/-- The targets miss no class: every class of out line a step from a state the step invariant holds of shows is aimed
at by some target, given rule names that list every rule an admission can name. -/
theorem classes_covered (T : List TypeDecl) {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV}
    (hv : v.Reach P E) {rules : RuleNames} (hr : RulesListed v rules) {s : State v} (hs : Step.Inv P s)
    (x : Input v) : ∀ c ∈ classes T v x (step T v s x), ∃ g ∈ targets T v rules, g.covers rules c = true := by
  intro c hc
  simp only [classes, List.mem_append, List.mem_map] at hc
  rcases hc with (hc | ⟨ev, -, rfl⟩) | ⟨o, ho, rfl⟩
  · cases x with
    | command i caller input =>
      obtain ⟨hinv, hrej⟩ := step_command_outcome (T := T) s i caller input
      have inCmd : ∀ g, g ∈ (GenTarget.accepted (v.commands.get i).name ::
          (variantsOf T (v.commands.get i).rejection).map (.rejected (v.commands.get i).name) ++
          invalidTargets rules (v.commands.get i).name) → g ∈ targets T v rules := fun g hg =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.2 ⟨_, List.get_mem _ _, hg⟩)))
      cases ho : (step T v s (.command i caller input)).outcome with
      | accepted =>
        rw [ho] at hc
        simp only [answerClasses, List.mem_singleton] at hc
        subst hc
        exact ⟨_, inCmd _ List.mem_cons_self, by simp [GenTarget.covers]⟩
      | rejected w =>
        rw [ho] at hc
        simp only [answerClasses, List.mem_singleton] at hc
        subst hc
        have h1 := hrej w ho
        obtain ⟨t, j⟩ := w
        simp only at h1
        subst h1
        exact ⟨_, inCmd _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.2 ⟨_, variantOf_mem T _ j, rfl⟩))), by simp [GenTarget.covers]⟩
      | invalid rs =>
        rw [ho] at hc
        simp only [answerClasses] at hc
        obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hc
        rw [hinv rs ho] at hn
        have hn' : n = "callers" ∨ some n ∈ rules (v.commands.get i).name ∨ none ∈ rules (v.commands.get i).name :=
          (mem_admit hn).elim .inl fun hb => .inr (hr.1 i input n hb)
        obtain ⟨g, hg, hcov⟩ := invalid_covered hn'
        exact ⟨g, inCmd _ (List.mem_cons_of_mem _ (List.mem_append_right _ hg)), hcov⟩
      | answered _ => rw [ho] at hc; simp [answerClasses] at hc
      | fault _ => rw [ho] at hc; simp [answerClasses] at hc
    | query i caller input =>
      have inQ : ∀ g, g ∈ (GenTarget.answered (v.queries.get i).name :: invalidTargets rules (v.queries.get i).name) →
          g ∈ targets T v rules := fun g hg =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨_, List.get_mem _ _, hg⟩)))
      cases ho : (step T v s (.query i caller input)).outcome with
      | answered _ =>
        rw [ho] at hc
        simp only [answerClasses, List.mem_singleton] at hc
        subst hc
        exact ⟨_, inQ _ List.mem_cons_self, by simp [GenTarget.covers]⟩
      | invalid rs =>
        rw [ho] at hc
        simp only [answerClasses] at hc
        obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hc
        rw [step_query_outcome (T := T) s i caller input rs ho] at hn
        have hn' : n = "callers" ∨ some n ∈ rules (v.queries.get i).name ∨ none ∈ rules (v.queries.get i).name :=
          (mem_admit hn).elim .inl fun hb => .inr (hr.2 i input n hb)
        obtain ⟨g, hg, hcov⟩ := invalid_covered hn'
        exact ⟨g, inQ _ (List.mem_cons_of_mem _ hg), hcov⟩
      | accepted => rw [ho] at hc; simp [answerClasses] at hc
      | rejected _ => rw [ho] at hc; simp [answerClasses] at hc
      | fault _ => rw [ho] at hc; simp [answerClasses] at hc
    | answer _ _ | event _ _ | clock _ => simp [answerClasses] at hc
  · exact ⟨.event (variantOf T v.event ev), List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨_, variantOf_mem T _ ev, rfl⟩)), by simp [GenTarget.covers]⟩
  · obtain ⟨p, hp, rfl⟩ := Step.step_outsWait T s x o ho
    obtain ⟨y, hy⟩ := (step_inv T hv s hs x).shaped p hp
    obtain ⟨sh, hsh, hx, hn⟩ := pendingOf_shape (shapes v) p.id y
    rw [hy] at hx hn
    exact ⟨.request sh.external sh.name, List.mem_append_right _
      ((mem_dedupBy (fun _ _ => beq_iff_eq) _ _).2 (List.mem_map.2 ⟨sh, hsh, rfl⟩)),
      by simp [GenTarget.covers, Step.Pending.line, hx, hn]⟩

/-- generate's targets miss no class: every class of out line a step from a state the step invariant holds of shows is
aimed at by one of the targets generate makes from the checked IR (`ruleNamesOf`). -/
theorem targets_cover (T : List TypeDecl) {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV}
    (hv : v.Reach P E) {s : State v} (hs : Step.Inv P s) (x : Input v) :
    ∀ c ∈ classes T v x (step T v s x), ∃ g ∈ targets T v (ruleNamesOf v), g.covers (ruleNamesOf v) c = true :=
  classes_covered T hv (rulesListed_ofIr v) hs x

end Tazuna.Ir
