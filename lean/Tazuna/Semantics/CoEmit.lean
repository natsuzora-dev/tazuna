import Tazuna.Semantics.Emits

/-! Which own effects one run of a function that returns effects can start together. A list of effects a reaction
returns holds the effects of one path through its code: a `case` takes one clause, and a list written in place holds
each of its items once. So two own effects the run starts at different places of the list are answered at a pair of
sites one path writes (`Co.pairs`), and an own effect is answered at a site the path writes (`Co.sites`). Where the
code is any other expression, the run can start any number of effects of any site the expression writes
(`Co.any`, read off `Expr.reach_live`). `Expr.co_ok` proves the reading for the variables of a run, which hold data. -/

namespace Tazuna.Ir

/-- The site of the kept function an own effect runs at its answer. -/
def OwnEffectV.site {e : Ty} : OwnEffectV e → SiteId
  | .command _ _ _ _ _ f => f.site
  | .query _ _ _ _ _ f => f.site

/-- What a list of effects can hold of own effects: the sites they are answered at, and the pairs of sites two of
them at different places can have, either way round. -/
structure Co where
  sites : List SiteId
  pairs : List (SiteId × SiteId)

namespace Co

def empty : Co := ⟨[], []⟩

/-- One effect answered at one of `ss`. -/
def one (ss : List SiteId) : Co := ⟨ss, []⟩

/-- Any number of own effects answered at the kept functions `ss`. -/
def any (ss : List AnySite) : Co :=
  let ids := ss.map (·.2.2.site)
  ⟨ids, ids.flatMap fun a => ids.map (a, ·)⟩

/-- What one of two alternatives holds. -/
def union (a b : Co) : Co := ⟨a.sites ++ b.sites, a.pairs ++ b.pairs⟩

/-- What `a` holds followed by what `b` holds. -/
def append (a b : Co) : Co :=
  ⟨a.sites ++ b.sites, a.pairs ++ b.pairs ++ a.sites.flatMap fun x => b.sites.map (x, ·)⟩

/-- Whether two own effects answered at `s1` and `s2` can be at two places. -/
def Rel (c : Co) (s1 s2 : SiteId) : Prop := (s1, s2) ∈ c.pairs ∨ (s2, s1) ∈ c.pairs

end Co

/-- The own effects of `xs` are answered at `c`'s sites, and two of them at different places at a pair of `c`. -/
def CoOk {e : Ty} (c : Co) (xs : List (EffectV e)) : Prop :=
  (∀ x ∈ xs, ∀ o, x.own? = some o → o.site ∈ c.sites) ∧
    xs.Pairwise fun x y => ∀ o1 o2, x.own? = some o1 → y.own? = some o2 → c.Rel o1.site o2.site

section
variable {e : Ty}

theorem CoOk.any {ss : List AnySite} {xs : List (EffectV e)}
    (h : ∀ x ∈ xs, ∀ o, x.own? = some o → o.site ∈ ss.map (·.2.2.site)) : CoOk (Co.any ss) xs := by
  refine ⟨h, List.pairwise_of_forall_mem_list fun x hx y hy o1 o2 h1 h2 => .inl ?_⟩
  exact List.mem_flatMap.2 ⟨_, h x hx o1 h1, List.mem_map.2 ⟨_, h y hy o2 h2, rfl⟩⟩

theorem CoOk.union_l {a b : Co} {xs : List (EffectV e)} (h : CoOk a xs) : CoOk (a.union b) xs :=
  ⟨fun x hx o ho => List.mem_append_left _ (h.1 x hx o ho),
    h.2.imp fun hr o1 o2 h1 h2 => (hr o1 o2 h1 h2).imp (List.mem_append_left _) (List.mem_append_left _)⟩

theorem CoOk.union_r {a b : Co} {xs : List (EffectV e)} (h : CoOk b xs) : CoOk (a.union b) xs :=
  ⟨fun x hx o ho => List.mem_append_right _ (h.1 x hx o ho),
    h.2.imp fun hr o1 o2 h1 h2 => (hr o1 o2 h1 h2).imp (List.mem_append_right _) (List.mem_append_right _)⟩

theorem CoOk.append {a b : Co} {xs ys : List (EffectV e)} (ha : CoOk a xs) (hb : CoOk b ys) :
    CoOk (a.append b) (xs ++ ys) := by
  refine ⟨fun x hx o ho => ?_, List.pairwise_append.2 ⟨?_, ?_, ?_⟩⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (ha.1 x hx o ho)
    · exact List.mem_append_right _ (hb.1 x hx o ho)
  · exact ha.2.imp fun hr o1 o2 h1 h2 =>
      (hr o1 o2 h1 h2).imp (fun h => List.mem_append_left _ (List.mem_append_left _ h))
        (fun h => List.mem_append_left _ (List.mem_append_left _ h))
  · exact hb.2.imp fun hr o1 o2 h1 h2 =>
      (hr o1 o2 h1 h2).imp (fun h => List.mem_append_left _ (List.mem_append_right _ h))
        (fun h => List.mem_append_left _ (List.mem_append_right _ h))
  · intro x hx y hy o1 o2 h1 h2
    exact .inl (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, ha.1 x hx o1 h1,
      List.mem_map.2 ⟨_, hb.1 y hy o2 h2, rfl⟩⟩))

theorem CoOk.one {ss : List SiteId} {x : EffectV e} (h : ∀ o, x.own? = some o → o.site ∈ ss) :
    CoOk (Co.one ss) [x] :=
  ⟨fun y hy o ho => by rw [List.mem_singleton.1 hy] at ho; exact h o ho, List.pairwise_singleton _ _⟩

theorem CoOk.empty : CoOk (e := e) Co.empty [] := ⟨fun _ h => (by cases h), List.Pairwise.nil⟩

/-- `CoOk` where the items are effects; nothing for items of another type. -/
def CoOkL (c : Co) (t : Ty) (xs : List t.den) : Prop :=
  ∀ e (h : t = .dsl .effect [e]), CoOk c (cast (congrArg (fun t => List t.den) h) xs)

/-- `CoOk` where the value is a list of effects; nothing for a value of another type. -/
def CoOkT (c : Co) (t : Ty) (x : t.den) : Prop :=
  ∀ u (h : t = .list u), CoOkL c u (cast (congrArg Ty.den h) x)

theorem CoOkL.union_l {a b : Co} {t : Ty} {xs : List t.den} (h : CoOkL a t xs) : CoOkL (a.union b) t xs := by
  intro e he; subst he; exact CoOk.union_l (h e rfl)

theorem CoOkL.union_r {a b : Co} {t : Ty} {xs : List t.den} (h : CoOkL b t xs) : CoOkL (a.union b) t xs := by
  intro e he; subst he; exact CoOk.union_r (h e rfl)

theorem CoOkT.union_l {a b : Co} {t : Ty} {x : t.den} (h : CoOkT a t x) : CoOkT (a.union b) t x := by
  intro u hu; subst hu; exact CoOkL.union_l (h u rfl)

theorem CoOkT.union_r {a b : Co} {t : Ty} {x : t.den} (h : CoOkT b t x) : CoOkT (a.union b) t x := by
  intro u hu; subst hu; exact CoOkL.union_r (h u rfl)

theorem CoOkL.append {a b : Co} {t : Ty} {xs ys : List t.den} (ha : CoOkL a t xs) (hb : CoOkL b t ys) :
    CoOkL (a.append b) t (xs ++ ys) := by
  intro e he; subst he; exact CoOk.append (ha e rfl) (hb e rfl)

/-- An effect that reaches `P` is answered at a site of `P`. -/
theorem own_site_of_reach {P : List AnySite} {x : EffectV e} (h : x.Reach P) :
    ∀ o, x.own? = some o → o.site ∈ P.map (·.2.2.site) := by
  intro o ho
  cases x with
  | request => cases ho
  | command => cases ho; exact List.mem_map.2 ⟨_, h, rfl⟩
  | query => cases ho; exact List.mem_map.2 ⟨_, h, rfl⟩

theorem CoOkT.any {E : List AnyEffectSite} {ss : List AnySite} {t : Ty} {x : t.den} (h : Reach ss E t x) :
    CoOkT (Co.any ss) t x := by
  intro u hu; subst hu; intro e he; subst he
  exact CoOk.any fun y hy => own_site_of_reach (h y hy)

end

section
variable {G : List Ty} (i : Nat) (ok : Nat → Bool) (D : Defs G)

/-- The kept functions an expression writes for allowed variables, with those of every global it reads
(`Expr.reach_live`). -/
def Expr.liveAll {Γ : List Ty} {t : Ty} (e : Expr G Γ t) : List AnySite :=
  Expr.liveSites i ok D e ++ (Expr.liveGlobals i ok D e).flatMap (D.usesAt sitesC)

/-- What an effect an expression returns can be answered at: the site of a `send_command` or `send_query` whose
`on_answer` is written in place, else any site the expression writes. -/
def Expr.oneCo {Γ : List Ty} {t : Ty} (e : Expr G Γ t) : Co :=
  match e with
  | .call f args => if sendPrim f then
      match args.closeSiteAt? 2 with
      | some s => Co.one [s]
      | none => Co.one ((e.liveAll i ok D).map (·.2.2.site))
    else Co.one ((e.liveAll i ok D).map (·.2.2.site))
  | e => Co.one ((e.liveAll i ok D).map (·.2.2.site))

mutual
/-- What the list of effects an expression returns can hold of own effects: a list written in place holds each item
once, a `case` or `let` over data that builds only allowed constructors (`Expr.okIn`) holds what one live clause
or its body holds, and anything else any effects of the sites it writes. -/
def Expr.co {Γ : List Ty} {t : Ty} : Expr G Γ t → Co
  | .list items => Items.co items
  | @Expr.case _ _ u _ _ x cs hc =>
    if x.okIn i ok D && u.isData then Clauses.co cs else Co.any ((Expr.case x cs hc).liveAll i ok D)
  | @Expr.let_ _ _ u _ x body =>
    if x.okIn i ok D && u.isData then Expr.co body else Co.any ((Expr.let_ x body).liveAll i ok D)
  | e => Co.any (e.liveAll i ok D)
def Items.co {Γ : List Ty} {t : Ty} : Items G Γ t → Co
  | .nil => Co.empty
  | .cons x xs => (x.oneCo i ok D).append (Items.co xs)
def Clauses.co {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → Co
  | .nil => Co.empty
  | .cons p body rest => (if p.live i ok then Expr.co body else Co.empty).union (Clauses.co rest)
  | .guarded p _ body rest => (if p.live i ok then Expr.co body else Co.empty).union (Clauses.co rest)
end

end

theorem Prim.sends_eq {p : Prim} (h : p.sends = true) : p = .sendCommand ∨ p = .sendQuery := by
  cases p <;> simp_all [Prim.sends]

/-- A `send_command` or `send_query` whose `on_answer` is written in place starts an effect answered there. -/
theorem send_site {G Γ ps : List Ty} {ev : Ty} (D : Defs G) (f : Expr G Γ (.fn ps (.dsl .effect [ev])))
    (args : Exprs G Γ ps) (hs : sendPrim f = true) {s : SiteId} (hc : args.closeSiteAt? 2 = some s)
    (ρ : Ty.dens Γ) : ∀ o, (Expr.eval D D.eval (.call f args) ρ).own? = some o → o.site = s := by
  unfold sendPrim at hs
  split at hs
  · rename_i p ts hp
    rcases Prim.sends_eq hs with rfl | rfl
    · rcases args with _ | ⟨n, _ | ⟨x, _ | ⟨oa, _ | ⟨_, _⟩⟩⟩⟩
      simp only [Exprs.closeSiteAt?, Expr.closeSite?] at hc
      split at hc
      · rename_i heq1 heq2
        cases hc
        intro o ho
        simp only [Prim.sig, Ty.inst, Ty.insts, Ty.dsl.injEq, List.cons.injEq, and_true, true_and] at ts heq1
        subst ts
        subst heq1
        cases eq_of_heq hp
        cases eq_of_heq heq2
        simp only [Expr.eval, Exprs.eval, Prim.den, EffectV.own?, Option.some.injEq] at ho
        subst ho
        rfl
      · cases hc
    · rcases args with _ | ⟨n, _ | ⟨x, _ | ⟨oa, _ | ⟨_, _⟩⟩⟩⟩
      simp only [Exprs.closeSiteAt?, Expr.closeSite?] at hc
      split at hc
      · rename_i heq1 heq2
        cases hc
        intro o ho
        simp only [Prim.sig, Ty.inst, Ty.insts, Ty.dsl.injEq, List.cons.injEq, and_true, true_and] at ts heq1
        subst ts
        subst heq1
        cases eq_of_heq hp
        cases eq_of_heq heq2
        simp only [Expr.eval, Exprs.eval, Prim.den, EffectV.own?, Option.some.injEq] at ho
        subst ho
        rfl
      · cases hc
  · cases hs

section
variable {i : Nat} {okV : Nat → Prop} {ok : Nat → Bool} {E : List AnyEffectSite} {G : List Ty} {D : Defs G}
  (hDE : ∀ s ∈ D.effectSites, s ∈ E) (hi : 15 ≤ i) (hok : ∀ k, okV k ↔ ok k = true)
include hDE hi hok

set_option linter.unusedSectionVars false

/-- Where its variables hold data built with allowed constructors, an expression's value reaches only the kept
functions it writes (`Expr.liveAll`). -/
theorem Expr.reach_liveAll {Γ : List Ty} {t : Ty} (e : Expr G Γ t) (he : ∀ s ∈ e.effectSites D, s ∈ E)
    (ρ : Ty.dens Γ) (hρ : ∀ P, Reaches P E Γ ρ) (hoρ : Oks i okV Γ ρ) :
    Reach (e.liveAll i ok D) E t (e.eval D D.eval ρ) :=
  Expr.reach_live (P := e.liveAll i ok D) (fun v h => Defs.reach _ D hDE v h) hDE hi hok e
    (fun _ h => List.mem_append_left _ h) (fun j hj _ hs => List.mem_append_right _ (List.mem_flatMap.2 ⟨j, hj, hs⟩))
    he ρ (hρ _) hoρ

theorem Expr.oneCo_ok {Γ : List Ty} {u : Ty} (e : Expr G Γ u) (he : ∀ s ∈ e.effectSites D, s ∈ E)
    (ρ : Ty.dens Γ) (hρ : ∀ P, Reaches P E Γ ρ) (hoρ : Oks i okV Γ ρ) :
    CoOkL (e.oneCo i ok D) u [e.eval D D.eval ρ] := by
  have hr := Expr.reach_liveAll hDE hi hok e he ρ hρ hoρ
  intro ev hu
  subst hu
  · have hdf : CoOk (Co.one ((e.liveAll i ok D).map (·.2.2.site))) [e.eval D D.eval ρ] :=
      CoOk.one (own_site_of_reach hr)
    unfold Expr.oneCo
    split
    · rename_i f args
      split
      · rename_i hs
        split
        · rename_i s hc
          exact CoOk.one fun o ho => by rw [send_site D f args hs hc ρ o ho]; exact List.mem_singleton_self _
        · exact hdf
      · exact hdf
    · exact hdf

theorem Expr.coAny_ok {Γ : List Ty} {t : Ty} (e : Expr G Γ t) (he : ∀ s ∈ e.effectSites D, s ∈ E)
    (ρ : Ty.dens Γ) (hρ : ∀ P, Reaches P E Γ ρ) (hoρ : Oks i okV Γ ρ) :
    CoOkT (Co.any (e.liveAll i ok D)) t (e.eval D D.eval ρ) :=
  CoOkT.any (Expr.reach_liveAll hDE hi hok e he ρ hρ hoρ)

mutual
/-- Where its variables hold data built with allowed constructors, the list of effects an expression returns holds
what `Expr.co` reads off it. -/
theorem Expr.co_ok {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) →
    (∀ s ∈ e.effectSites D, s ∈ E) → (ρ : Ty.dens Γ) → (∀ P, Reaches P E Γ ρ) → Oks i okV Γ ρ →
    CoOkT (e.co i ok D) t (e.eval D D.eval ρ)
  | .list items, he, ρ, hρ, hoρ => fun u hu => by
    cases hu
    exact Items.co_ok items (by simpa [Expr.effectSites] using he) ρ hρ hoρ
  | @Expr.case _ _ u _ _ x cs hc, he, ρ, hρ, hoρ => by
    simp only [Expr.co]
    split
    · rename_i hk
      simp only [Bool.and_eq_true] at hk
      have he' := he
      simp only [Expr.effectSites] at he'
      have hox := Expr.okIn_ok (P := []) (fun v h => Defs.reach _ D hDE v h) hDE hi hok x hk.1 ρ hoρ
      exact Clauses.co_ok cs (sub_r he') ρ hρ hoρ _ hk.2 hox _
    · exact Expr.coAny_ok hDE hi hok _ he ρ hρ hoρ
  | @Expr.let_ _ _ u _ x body, he, ρ, hρ, hoρ => by
    simp only [Expr.co]
    split
    · rename_i hk
      simp only [Bool.and_eq_true] at hk
      have he' := he
      simp only [Expr.effectSites] at he'
      have hox := Expr.okIn_ok (P := []) (fun v h => Defs.reach _ D hDE v h) hDE hi hok x hk.1 ρ hoρ
      exact Expr.co_ok body (sub_r he') _ (fun P => ⟨reach_data P u hk.2 _, hρ P⟩) ⟨hox, hoρ⟩
    · exact Expr.coAny_ok hDE hi hok _ he ρ hρ hoρ
  | .int _, he, ρ, hρ, hoρ | .str _, he, ρ, hρ, hoρ | .var _, he, ρ, hρ, hoρ | .global _, he, ρ, hρ, hoρ
  | .ctor .., he, ρ, hρ, hoρ | .field .., he, ρ, hρ, hoρ | .index .., he, ρ, hρ, hoρ | .update .., he, ρ, hρ, hoρ
  | .call .., he, ρ, hρ, hoρ | .lam _, he, ρ, hρ, hoρ | .tuple _, he, ρ, hρ, hoρ | .bin .., he, ρ, hρ, hoρ
  | .not _, he, ρ, hρ, hoρ | .neg _, he, ρ, hρ, hoρ | .prim .., he, ρ, hρ, hoρ | .close .., he, ρ, hρ, hoρ
  | .closeEffect .., he, ρ, hρ, hoρ => Expr.coAny_ok hDE hi hok _ he ρ hρ hoρ
theorem Items.co_ok {Γ : List Ty} {u : Ty} : (items : Items G Γ u) →
    (∀ s ∈ Items.effectSites D items, s ∈ E) → (ρ : Ty.dens Γ) → (∀ P, Reaches P E Γ ρ) → Oks i okV Γ ρ →
    CoOkL (Items.co i ok D items) u (Items.eval D D.eval items ρ)
  | .nil, _, _, _, _ => fun _ h => by subst h; exact CoOk.empty
  | .cons x xs, he, ρ, hρ, hoρ => by
    simp only [Items.effectSites] at he
    exact CoOkL.append (Expr.oneCo_ok hDE hi hok x (sub_l he) ρ hρ hoρ) (Items.co_ok xs (sub_r he) ρ hρ hoρ)
theorem Clauses.co_ok {Γ : List Ty} {t r : Ty} {sh : List Shape} :
    (cs : Clauses G Γ t r sh) → (∀ s ∈ Clauses.effectSites D cs, s ∈ E) →
    (ρ : Ty.dens Γ) → (∀ P, Reaches P E Γ ρ) → Oks i okV Γ ρ → (x : t.den) → t.isData = true → Ok i okV t x →
    (h : ∃ s ∈ sh, Shape.Matches t s x) → CoOkT (Clauses.co i ok D cs) r (Clauses.eval D D.eval cs ρ x h)
  | .nil, _, _, _, _, _, _, _, h => False.elim (by simp at h)
  | .cons p body rest, he, ρ, hρ, hoρ, x, hd, hox, h => by
    simp only [Clauses.effectSites] at he
    simp only [Clauses.eval]
    split
    · rename_i δ hm
      have hl := Pat.live_of_match (fun k => (hok k).1) p x hm hox
      simp only [Clauses.co, hl, ite_true]
      exact CoOkT.union_l (Expr.co_ok body (sub_l he) _
        (fun P => Dens.reach_append P δ ρ (Pat.reach_match P p x hm (reach_data P _ hd x)) (hρ P))
        (Dens.ok_append δ ρ (Pat.ok_match p x hm hox) hoρ))
    · simp only [Clauses.co]
      exact CoOkT.union_r (Clauses.co_ok rest (sub_r he) ρ hρ hoρ x hd hox _)
  | .guarded p guard body rest, he, ρ, hρ, hoρ, x, hd, hox, h => by
    simp only [Clauses.effectSites] at he
    simp only [Clauses.eval]
    split
    · rename_i δ hm
      have hl := Pat.live_of_match (fun k => (hok k).1) p x hm hox
      split
      · simp only [Clauses.co, hl, ite_true]
        exact CoOkT.union_l (Expr.co_ok body (sub_r (sub_l he)) _
          (fun P => Dens.reach_append P δ ρ (Pat.reach_match P p x hm (reach_data P _ hd x)) (hρ P))
          (Dens.ok_append δ ρ (Pat.ok_match p x hm hox) hoρ))
      · simp only [Clauses.co]
        exact CoOkT.union_r (Clauses.co_ok rest (sub_r he) ρ hρ hoρ x hd hox h)
    · simp only [Clauses.co]
      exact CoOkT.union_r (Clauses.co_ok rest (sub_r he) ρ hρ hoρ x hd hox h)
end

end

/-- What a function that returns effects starts for allowed arguments (`Expr.co` of a function written in place). -/
def EffectFun.co (i : Nat) (ok : Nat → Bool) {ps : List Ty} {r : Ty} (f : EffectFun ps r) : Co :=
  match f.body with
  | .lam body => body.co i ok f.defs
  | _ => Co.any (f.liveUses i ok)

/-- A function that returns a list of effects starts, for allowed arguments, what `EffectFun.co` reads off it, where
the values it captured cannot hold a value of the declaration `i`. -/
theorem EffectFun.co_ok {i : Nat} {okV : Nat → Prop} {ok : Nat → Bool} (hi : 15 ≤ i)
    (hok : ∀ k, okV k ↔ ok k = true) {P : List AnySite} {E : List AnyEffectSite} {ps : List Ty} {ev : Ty}
    (f : EffectFun ps (.list (.dsl .effect [ev]))) (hf : f.Reach P E) (hΓ : (Ty.tuple f.Γ).mentions i = false)
    (xs : (Ty.tuple ps).den0) (hxs : Oks i okV ps (Ty.up _ f.hps xs)) : CoOk (f.co i ok) (f.apply xs) := by
  have hdf := EffectFun.reach_live hi hok f hf (P' := f.liveUses i ok) (fun _ h => h) hΓ xs hxs
  change Tazuna.Ir.Reach (f.body.liveUses i ok f.defs) E _
    (f.body.eval f.defs f.defs.eval (Ty.up _ f.hΓ f.env) (Ty.up _ f.hps xs)) at hdf
  have hu := hf.effectSites
  have hρ : ∀ P', Reaches P' E f.Γ (Ty.up _ f.hΓ f.env) := fun P' => reach_data P' (.tuple f.Γ) f.hΓ _
  have hps : ∀ P', Reaches P' E ps (Ty.up _ f.hps xs) := fun P' => reach_data P' (.tuple ps) f.hps _
  revert hdf hu
  unfold EffectFun.co EffectFun.apply EffectFun.liveUses
  generalize f.body = body
  intro hdf hu
  split
  · exact Expr.co_ok hf.defsEffectSites hi hok _ (by simpa [Expr.effectSites] using hu) _
      (fun P' => Dens.reach_append P' _ _ (hps P') (hρ P')) (Dens.ok_append _ _ hxs (oks_free _ hΓ _)) _ rfl _ rfl
  · exact CoOk.any fun y hy => own_site_of_reach (hdf y hy)

/-- What the reactions `ys` start for one event: each reaction's own effects (`EffectFun.co`), and any effect of one
reaction with any effect of a later one. -/
def reactionsCo (i : Nat) (ok : Nat → Bool) {r e : Ty} : List (ReactionV r e) → Co
  | [] => Co.empty
  | y :: ys => (y.react.co i ok).append (reactionsCo i ok ys)

namespace Step

/-- The waiting own effects of a step in progress: two of them, where neither is answered at a site of `C` (whose
effects a step may start any number of), are answered at a pair `c` allows. -/
def QueueCo {v : ServiceV} (C : List SiteId) (c : Co) (a : Acc v) : Prop :=
  a.own.Pairwise fun o1 o2 => o1.site ∈ C ∨ o2.site ∈ C ∨ c.Rel o1.site o2.site

variable (T : List TypeDecl) {v : ServiceV}

theorem start_own_eq (a : Acc v) (effs : List (Sender × EffectV v.event)) {a' : Acc v} (h : start a effs = .ok a') :
    a'.own = a.own ++ effs.filterMap (·.2.own?) := by
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; simp [← h]
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      rw [ih a1 h]
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · intro h1; cases h1; simp [EffectV.own?]
      | command => intro h1; cases h1; simp [EffectV.own?]
      | query => intro h1; cases h1; simp [EffectV.own?]

theorem _root_.Tazuna.Ir.OwnEffectV.site_of_reach {P : List AnySite} {o : OwnEffectV v.event} (h : o.effect.Reach P) :
    o.site ∈ P.map (·.2.2.site) := by
  cases o <;> exact List.mem_map.2 ⟨_, h, rfl⟩

section
variable {i : Nat} {okV : Nat → Prop} {ok : Nat → Bool} {P : List AnySite} {E : List AnyEffectSite}
  (hi : 15 ≤ i) (hq : Quiet i v) (hv : v.Reach P E) (hok : ∀ k, okV k ↔ ok k = true)
include hi hq hv hok

set_option linter.unusedSectionVars false

/-- An instance entering a state starts effects answered at the sites its machine's `effect` writes in a step without
a clock line (`MachineV.liveSites`). -/
theorem enter_machine {m : MachineV v.records v.event} (hm : m ∈ v.machines) (records : v.records.den0) (now : Int)
    (key : m.key.den0) (st : m.state.den0) (hst : ∀ j ns, m.enters = some (j, ns) →
      ∀ h : m.state.isData = true, Ok j (· ∈ ns) m.state (Ty.up _ h st)) :
    EffsReach (m.liveSites false) (enter m records now key st).2 := by
  intro x hx
  simp only [enter, List.mem_map, Option.mem_toList] at hx
  obtain ⟨eff, heff, rfl⟩ := hx
  have hr := (hv.machines m hm).effect
  cases hen : m.enters with
  | none =>
    simp only [MachineV.liveSites, hen]
    exact MachineV.reach_effectAt _ m ⟨hr.site, fun _ h => h, hr.effectSites, hr.defsEffectSites⟩ key st records
      now eff heff
  | some p =>
    obtain ⟨j, ns⟩ := p
    simp only [MachineV.liveSites, hen]
    exact MachineV.reach_live_effectAt m hr hen (fun _ h => h) key st records now (hst j ns hen) eff heff

/-- One event's reactions start, together, what `reactionsCo` reads off them. -/
theorem reactions_co (ev : v.event.den0) (hev : ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev))
    (records : v.records.den0) (now : Int) : (ys : List (ReactionV v.records v.event)) → (∀ y ∈ ys, y ∈ v.reactions) →
    CoOk (reactionsCo i ok ys) (ys.flatMap fun y => y.effectsAt ev records now)
  | [], _ => CoOk.empty
  | y :: ys, hys => by
    have hy := hys y List.mem_cons_self
    refine CoOk.append ?_ (reactions_co ev hev records now ys fun z hz => hys z (List.mem_cons_of_mem _ hz))
    exact EffectFun.co_ok hi hok y.react (hv.reactions y hy) (hq.reactions y hy) (.inl (records, now, ()), ev, ())
      (oks_up_cons _ _ _ (fun _ => ok_free _ (by
        simp [Ty.reactionCtx, Ty.mentionsL, Ty.mentions, Ty.mentionsLL, hq.records]; omega) _)
        (fun _ => oks_up_cons _ _ _ hev (fun _ => trivial)))

/-- The cascade of one event, from a step in progress with nothing waiting, starts with own effects a machine's
`effect` writes (`C` holds their sites) or that the reactions start together (`reactionsCo`). -/
theorem event_queueCo {C : List SiteId} (hC : ∀ m ∈ v.machines, ∀ s ∈ m.liveSites false, s.2.2.site ∈ C)
    (s : State v) (ev : v.event.den0) (hev : ∀ h : v.event.isData = true, Ok i okV v.event (Ty.up _ h ev))
    {a : Acc v} (h : applyEvents T { state := s } [ev] = .ok a) :
    QueueCo C (reactionsCo i ok v.reactions) a := by
  simp only [applyEvents, List.foldlM_cons, List.foldlM_nil, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i a1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [QueueCo, start_own_eq _ _ h1, List.nil_append, List.pairwise_filterMap]
    let records := v.apply.fn (.inl (s.records, s.now, ()), ev, ())
    have hm := mem_reactMachines_effs T records s.now ev s.machines
    have hmach : ∀ x ∈ (reactMachines T records s.now ev s.machines).2, ∀ o, x.2.own? = some o → o.site ∈ C := by
      intro x hx o ho
      obtain ⟨sm, hsm, h⟩ := hm x hx
      simp only [machineStep, List.mem_flatMap, List.mem_map] at h
      obtain ⟨_, ⟨k, -, rfl⟩, h⟩ := h
      have hsm' := PerMachine.fst_mem hsm
      have key : ∀ (key : sm.1.key.den0) (st : sm.1.state.den0), (∀ j ns, sm.1.enters = some (j, ns) →
          ∀ h : sm.1.state.isData = true, Ok j (· ∈ ns) sm.1.state (Ty.up _ h st)) →
          x ∈ (enter sm.1 records s.now key st).2 → o.site ∈ C := fun key st hst hx' => by
        have hr := own_site_of_reach (enter_machine hi hq hv hok hsm' records s.now key st hst x hx') o ho
        obtain ⟨z, hz, hzs⟩ := List.mem_map.1 hr
        exact hzs ▸ hC _ hsm' z hz
      revert h
      unfold reactKey
      split
      · split
        · rename_i hon
          exact key _ _ fun _ _ hen hs => MachineV.on_enters hen _ hon hs
        · intro h; cases h
      · exact key _ _ fun _ _ hen hs => (MachineV.enters_some hen).2.1 hs
    have hre := reactions_co hi hq hv hok ev hev records s.now v.reactions (fun _ h => h)
    have hsplit : (react T s ev).2 = (reactMachines T records s.now ev s.machines).2 ++
        v.reactions.flatMap fun y => (y.effectsAt ev records s.now).map (.reaction y.name, ·) := rfl
    rw [hsplit, List.pairwise_append]
    refine ⟨List.pairwise_of_forall_mem_list fun x hx y _ o1 h1 o2 _ => .inl (hmach x hx o1 h1), ?_, ?_⟩
    · have hl : (v.reactions.flatMap fun y => (y.effectsAt ev records s.now).map (Sender.reaction y.name, ·)).map
          (·.2) = v.reactions.flatMap fun y => y.effectsAt ev records s.now := by
        simp [List.map_flatMap, Function.comp_def]
      have h2 := hre.2
      rw [← hl, List.pairwise_map] at h2
      exact h2.imp fun hr o1 ho1 o2 ho2 => .inr (.inr (hr o1 o2 ho1 ho2))
    · intro x hx y _ o1 h1 o2 _
      exact .inl (hmach x hx o1 (by simpa using h1))

/-- An internal step of the cascade keeps `QueueCo`: the effects it starts are answered at sites the cascade's
functions write for the events it can apply (`C` holds their sites), however many. -/
theorem queueCo_pick (hc : ∀ k ∈ v.cascadeEvs i, okV k) {C : List SiteId} {c : Co}
    (hC : ∀ s ∈ v.liveSites i ok false, s.2.2.site ∈ C) {a : Acc v} (ha : QueueCo C c a) {j : Nat}
    (hj : j < a.own.length) (he : EffOk i okV a.own[j].effect) {a' : Acc v}
    (h : runOwn T { a with own := a.own.eraseIdx j } a.own[j] = .ok a') : QueueCo C c a' := by
  have hfr : ({ a with own := a.own.eraseIdx j } : Acc v) = Acc.ownFront (a.own.eraseIdx j) { a with own := [] } := by
    simp [Acc.ownFront]
  rw [hfr, runOwn_own] at h
  cases hb : runOwn T { a with own := [] } a.own[j] with
  | error => simp [hb, Except.map] at h
  | ok b =>
    simp only [hb, Except.map, Except.ok.injEq] at h
    subst h
    have hq' := runOwn_live T hi hq hc hv hok (clock := false) (P' := v.liveSites i ok false) (fun _ h => h)
      { a with own := [] } (fun _ h => by cases h) _ he hb
    have hin : ∀ o ∈ b.own, o.site ∈ C := fun o ho => by
      obtain ⟨z, hz, hzs⟩ := List.mem_map.1 (OwnEffectV.site_of_reach (hq' o ho))
      exact hzs ▸ hC z hz
    simp only [QueueCo, Acc.ownFront]
    refine List.pairwise_append.2 ⟨ha.sublist (List.eraseIdx_sublist _ _),
      List.pairwise_of_forall_mem_list fun o1 h1 _ _ => .inl (hin o1 h1), fun _ _ o2 h2 => .inr (.inl (hin o2 h2))⟩

end

/-- The sites of `P` that take one value and return events: where an effect's `on_answer` is written. -/
def _root_.Tazuna.Ir.answerSites (P : List AnySite) (e : Ty) : List AnySite :=
  P.filter fun s => match s.2.1 with
    | .fn [_] r => (Ty.same r (.list e)).isSome
    | _ => false

/-- An effect whose `on_answer` is written at an answer site that captures no value of the declaration `i` and
builds only allowed constructors returns only allowed events. -/
theorem effOk_of_answer {P : List AnySite} {i : Nat} {okV : Nat → Prop} (hi : 15 ≤ i)
    (hP : ∀ s ∈ answerSites P v.event, (Ty.tuple s.1).mentions i = false ∧
      ∀ k ∈ s.2.2.body.evs i (s.2.2.defs.evs i), okV k)
    {eff : OwnEffectV v.event} (h : eff.effect.Reach P) : EffOk i okV eff.effect := by
  have key : ∀ {u : Ty} (f : Fun (Ty.fn [u] (.list v.event))), f.asSite ∈ P → u.mentions i = false →
      ∀ y, ∀ z ∈ Ty.listItems ((Fun.eval f : (Ty.fn [u] (.list v.event)).den) y), Ok i okV v.event z := by
    intro u f hf hu y z hz
    have hmem : f.asSite ∈ answerSites P v.event := List.mem_filter.2 ⟨hf, by
      simp only [Fun.asSite]; exact Ty_same_self _⟩
    obtain ⟨hΓ, hev⟩ := hP _ hmem
    exact Fun.ok_eval hi f hev (oks_free _ hΓ _) y (oks_free _ (by simp [Ty.mentionsL, hu]) y) z hz
  cases eff with
  | command n c inp j value f =>
    intro hj
    exact key f h (by simp only [Ty.result, Ty.nil, Ty.mentions, Ty.mentionsL, Ty.mentionsLL, hj]; simp; omega)
  | query n c inp o value f => exact key f h

end Step

end Tazuna.Ir
