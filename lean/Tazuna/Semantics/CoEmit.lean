import Tazuna.Semantics.Emits

/-! Which own effects one run of a function that returns effects can start together, and with which inputs. A list of
effects a reaction returns holds the effects of one path through its code: a `case` takes one clause, and a list
written in place holds each of its items once. So two own effects the run starts at different places of the list are
answered at a pair of sites one path writes (`Co.pairs`), and an own effect is answered at a site the path writes, with
an input whose constructors and integer literals the `send_command` or `send_query` writes (`Co.items`, `SPat`). Where
the code is any other expression, the run can start any number of effects of any site the expression writes, with any
input (`Co.any`, read off `Expr.reach_live`). `Expr.co_ok` proves the reading for the variables of a run, which hold
data. -/

namespace Tazuna.Ir

/-- The site of the kept function an own effect runs at its answer. -/
def OwnEffectV.site {e : Ty} : OwnEffectV e → SiteId
  | .command _ _ _ _ _ f => f.site
  | .query _ _ _ _ _ f => f.site

/-- What an expression's value can be, read off the constructors and integer literals it writes: anything, an
integer, or a constructor with what its fields can be. -/
inductive SPat where
  | any
  | int (n : Int)
  | ctor (k : Nat) (fs : List SPat)

mutual
def SPat.decEq : (a b : SPat) → Decidable (a = b)
  | .any, .any => isTrue rfl
  | .int n, .int m => if h : n = m then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .ctor k fs, .ctor k' fs' =>
    if hk : k = k' then
      match SPat.decEqs fs fs' with
      | isTrue h => isTrue (by rw [hk, h])
      | isFalse h => isFalse fun e => by cases e; exact h rfl
    else isFalse fun e => by cases e; exact hk rfl
  | .any, .int _ | .any, .ctor .. | .int _, .any | .int _, .ctor .. | .ctor .., .any | .ctor .., .int _ =>
    isFalse fun e => by cases e
def SPat.decEqs : (a b : List SPat) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match SPat.decEq a b, SPat.decEqs as bs with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse fun e => by cases e; exact h rfl
    | _, isFalse h' => isFalse fun e => by cases e; exact h' rfl
  | [], _ :: _ | _ :: _, [] => isFalse fun e => by cases e
end

instance : DecidableEq SPat := SPat.decEq

mutual
/-- Whether a value is what the pattern says. -/
def SPat.Fits : SPat → (t : Ty) → t.den → Prop
  | .int n, .int, x => x = n
  | .ctor k fs, .adt _ _ vs, x => ∃ v y, x = Alts.inj v y ∧ v.val = k ∧ SPat.Fitss fs (vs.get v) y
  | _, _, _ => True
def SPat.Fitss : List SPat → (ts : List Ty) → Ty.dens ts → Prop
  | p :: ps, t :: ts, (x, xs) => p.Fits t x ∧ SPat.Fitss ps ts xs
  | _, _, _ => True
end

/-- What every pattern of `ps` allows: the pattern where they are all the same, else anything. -/
def SPat.common : List SPat → SPat
  | [] => .any
  | p :: ps => if ps.all (fun q => decide (q = p)) then p else .any

theorem SPat.fits_any {t : Ty} {x : t.den} : SPat.any.Fits t x := by
  unfold SPat.Fits; trivial

theorem SPat.common_fits {ps : List SPat} {p : SPat} (hp : p ∈ ps) {t : Ty} {x : t.den} (h : p.Fits t x) :
    (SPat.common ps).Fits t x := by
  cases ps with
  | nil => cases hp
  | cons q qs =>
    simp only [SPat.common]
    split
    · rename_i hall
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h
      · have := List.all_eq_true.1 hall p hp
        simp only [decide_eq_true_eq] at this
        exact this ▸ h
    · exact SPat.fits_any

/-- The input of an own effect is what the pattern says. -/
def OwnEffectV.Fits {e : Ty} : OwnEffectV e → SPat → Prop
  | .command _ _ i _ value _, p => ∀ h : i.isData = true, p.Fits i (Ty.up i h value)
  | .query _ _ i _ value _, p => ∀ h : i.isData = true, p.Fits i (Ty.up i h value)

theorem OwnEffectV.fits_any {e : Ty} (o : OwnEffectV e) : o.Fits .any := by
  cases o <;> exact fun _ => SPat.fits_any

theorem OwnEffectV.fits_common {e : Ty} {o : OwnEffectV e} {ps : List SPat} {p : SPat} (hp : p ∈ ps)
    (h : o.Fits p) : o.Fits (SPat.common ps) := by
  cases o <;> exact fun hd => SPat.common_fits hp (h hd)

section
variable {G : List Ty}

mutual
/-- What the value an expression builds can be (`SPat`). -/
def Expr.spat {Γ : List Ty} {t : Ty} : Expr G Γ t → SPat
  | .int n => .int n
  | .ctor v es => .ctor v.val (Exprs.spats es)
  | _ => .any
def Exprs.spats {Γ ts : List Ty} : Exprs G Γ ts → List SPat
  | .nil => []
  | .cons e es => Expr.spat e :: Exprs.spats es
end

/-- What the `k`th expression builds can be. -/
def Exprs.spatAt {Γ : List Ty} : {ts : List Ty} → Exprs G Γ ts → Nat → SPat
  | _, .nil, _ => .any
  | _, .cons e _, 0 => e.spat
  | _, .cons _ es, k + 1 => es.spatAt k

variable (D : Defs G) (g : Ty.dens G)

mutual
theorem Expr.spat_fits {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → (ρ : Ty.dens Γ) → e.spat.Fits t (e.eval D g ρ)
  | .int _, _ => rfl
  | .ctor v es, ρ => ⟨v, _, rfl, rfl, Exprs.spats_fits es ρ⟩
  | .str _, _ | .var _, _ | .global _, _ | .field .., _ | .index .., _ | .update .., _ | .call .., _ | .lam _, _
  | .let_ .., _ | .case .., _ | .list _, _ | .tuple _, _ | .bin .., _ | .not _, _ | .neg _, _ | .prim .., _
  | .close .., _ | .closeEffect .., _ => SPat.fits_any
theorem Exprs.spats_fits {Γ ts : List Ty} : (es : Exprs G Γ ts) → (ρ : Ty.dens Γ) →
    SPat.Fitss (Exprs.spats es) ts (Exprs.eval D g es ρ)
  | .nil, _ => by simp [SPat.Fitss]
  | .cons e es, ρ => ⟨Expr.spat_fits e ρ, Exprs.spats_fits es ρ⟩
end

end

/-- What a list of effects can hold of own effects: the sites they are answered at with what their inputs can be, and
the pairs of sites two of them at different places can have, either way round. -/
structure Co where
  items : List (SiteId × SPat)
  pairs : List (SiteId × SiteId)

namespace Co

def sites (c : Co) : List SiteId := c.items.map (·.1)

def empty : Co := ⟨[], []⟩

/-- One effect answered at one of `ss`, with any input. -/
def one (ss : List SiteId) : Co := ⟨ss.map (·, .any), []⟩

/-- Any number of own effects answered at the kept functions `ss`, with any inputs. -/
def any (ss : List AnySite) : Co :=
  let ids := ss.map (·.2.2.site)
  ⟨ids.map (·, .any), ids.flatMap fun a => ids.map (a, ·)⟩

/-- What one of two alternatives holds. -/
def union (a b : Co) : Co := ⟨a.items ++ b.items, a.pairs ++ b.pairs⟩

/-- What `a` holds followed by what `b` holds. -/
def append (a b : Co) : Co :=
  ⟨a.items ++ b.items, a.pairs ++ b.pairs ++ a.sites.flatMap fun x => b.sites.map (x, ·)⟩

/-- Whether two own effects answered at `s1` and `s2` can be at two places. -/
def Rel (c : Co) (s1 s2 : SiteId) : Prop := (s1, s2) ∈ c.pairs ∨ (s2, s1) ∈ c.pairs

end Co

/-- The own effects of `xs` are as an item of `c` says, and two of them at different places at a pair of `c`. -/
def CoOk {e : Ty} (c : Co) (xs : List (EffectV e)) : Prop :=
  (∀ x ∈ xs, ∀ o, x.own? = some o → ∃ p, (o.site, p) ∈ c.items ∧ o.Fits p) ∧
    xs.Pairwise fun x y => ∀ o1 o2, x.own? = some o1 → y.own? = some o2 → c.Rel o1.site o2.site

section
variable {e : Ty}

theorem Co.mem_sites {c : Co} {s : SiteId} {p : SPat} (h : (s, p) ∈ c.items) : s ∈ c.sites :=
  List.mem_map.2 ⟨_, h, rfl⟩

theorem CoOk.any {ss : List AnySite} {xs : List (EffectV e)}
    (h : ∀ x ∈ xs, ∀ o, x.own? = some o → o.site ∈ ss.map (·.2.2.site)) : CoOk (Co.any ss) xs := by
  refine ⟨fun x hx o ho => ⟨.any, List.mem_map.2 ⟨_, h x hx o ho, rfl⟩, o.fits_any⟩,
    List.pairwise_of_forall_mem_list fun x hx y hy o1 o2 h1 h2 => .inl ?_⟩
  exact List.mem_flatMap.2 ⟨_, h x hx o1 h1, List.mem_map.2 ⟨_, h y hy o2 h2, rfl⟩⟩

theorem CoOk.union_l {a b : Co} {xs : List (EffectV e)} (h : CoOk a xs) : CoOk (a.union b) xs :=
  ⟨fun x hx o ho => (h.1 x hx o ho).imp fun _ h => ⟨List.mem_append_left _ h.1, h.2⟩,
    h.2.imp fun hr o1 o2 h1 h2 => (hr o1 o2 h1 h2).imp (List.mem_append_left _) (List.mem_append_left _)⟩

theorem CoOk.union_r {a b : Co} {xs : List (EffectV e)} (h : CoOk b xs) : CoOk (a.union b) xs :=
  ⟨fun x hx o ho => (h.1 x hx o ho).imp fun _ h => ⟨List.mem_append_right _ h.1, h.2⟩,
    h.2.imp fun hr o1 o2 h1 h2 => (hr o1 o2 h1 h2).imp (List.mem_append_right _) (List.mem_append_right _)⟩

theorem CoOk.append {a b : Co} {xs ys : List (EffectV e)} (ha : CoOk a xs) (hb : CoOk b ys) :
    CoOk (a.append b) (xs ++ ys) := by
  refine ⟨fun x hx o ho => ?_, List.pairwise_append.2 ⟨?_, ?_, ?_⟩⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact (ha.1 x hx o ho).imp fun _ h => ⟨List.mem_append_left _ h.1, h.2⟩
    · exact (hb.1 x hx o ho).imp fun _ h => ⟨List.mem_append_right _ h.1, h.2⟩
  · exact ha.2.imp fun hr o1 o2 h1 h2 =>
      (hr o1 o2 h1 h2).imp (fun h => List.mem_append_left _ (List.mem_append_left _ h))
        (fun h => List.mem_append_left _ (List.mem_append_left _ h))
  · exact hb.2.imp fun hr o1 o2 h1 h2 =>
      (hr o1 o2 h1 h2).imp (fun h => List.mem_append_left _ (List.mem_append_right _ h))
        (fun h => List.mem_append_left _ (List.mem_append_right _ h))
  · intro x hx y hy o1 o2 h1 h2
    obtain ⟨_, hp1, -⟩ := ha.1 x hx o1 h1
    obtain ⟨_, hp2, -⟩ := hb.1 y hy o2 h2
    exact .inl (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, Co.mem_sites hp1,
      List.mem_map.2 ⟨_, Co.mem_sites hp2, rfl⟩⟩))

theorem CoOk.one {ss : List SiteId} {x : EffectV e} (h : ∀ o, x.own? = some o → o.site ∈ ss) :
    CoOk (Co.one ss) [x] :=
  ⟨fun y hy o ho => by
    rw [List.mem_singleton.1 hy] at ho
    exact ⟨.any, List.mem_map.2 ⟨_, h o ho, rfl⟩, o.fits_any⟩, List.pairwise_singleton _ _⟩

theorem CoOk.send {s : SiteId} {p : SPat} {x : EffectV e} (h : ∀ o, x.own? = some o → o.site = s ∧ o.Fits p) :
    CoOk ⟨[(s, p)], []⟩ [x] :=
  ⟨fun y hy o ho => by
    rw [List.mem_singleton.1 hy] at ho
    exact ⟨p, by rw [(h o ho).1]; exact List.mem_singleton_self _, (h o ho).2⟩, List.pairwise_singleton _ _⟩

theorem CoOk.empty : CoOk (e := e) Co.empty [] := ⟨fun _ h => (by cases h), List.Pairwise.nil⟩

/-- `CoOk` where the items are effects; nothing for items of another type. -/
def CoOkL (c : Co) (t : Ty) (xs : List t.den) : Prop :=
  ∀ e (h : t = .dsl .effect [e]), CoOk c (cast (congrArg (fun t => List t.den) h) xs)

/-- `CoOk` where the value is a list of effects, or an optional effect; nothing for a value of another type. -/
def CoOkT (c : Co) (t : Ty) (x : t.den) : Prop :=
  (∀ u (h : t = .list u), CoOkL c u (cast (congrArg Ty.den h) x)) ∧
    ∀ u (h : t = Ty.option u), CoOkL c u (Ty.toOption (cast (congrArg Ty.den h) x)).toList

theorem CoOkL.union_l {a b : Co} {t : Ty} {xs : List t.den} (h : CoOkL a t xs) : CoOkL (a.union b) t xs := by
  intro e he; subst he; exact CoOk.union_l (h e rfl)

theorem CoOkL.union_r {a b : Co} {t : Ty} {xs : List t.den} (h : CoOkL b t xs) : CoOkL (a.union b) t xs := by
  intro e he; subst he; exact CoOk.union_r (h e rfl)

theorem CoOkT.union_l {a b : Co} {t : Ty} {x : t.den} (h : CoOkT a t x) : CoOkT (a.union b) t x :=
  ⟨fun u hu => by subst hu; exact CoOkL.union_l (h.1 u rfl), fun u hu => by subst hu; exact CoOkL.union_l (h.2 u rfl)⟩

theorem CoOkT.union_r {a b : Co} {t : Ty} {x : t.den} (h : CoOkT b t x) : CoOkT (a.union b) t x :=
  ⟨fun u hu => by subst hu; exact CoOkL.union_r (h.1 u rfl), fun u hu => by subst hu; exact CoOkL.union_r (h.2 u rfl)⟩

theorem CoOkL.append {a b : Co} {t : Ty} {xs ys : List t.den} (ha : CoOkL a t xs) (hb : CoOkL b t ys) :
    CoOkL (a.append b) t (xs ++ ys) := by
  intro e he; subst he; exact CoOk.append (ha e rfl) (hb e rfl)

theorem CoOkL.empty {t : Ty} : CoOkL Co.empty t [] := fun _ h => by subst h; exact CoOk.empty

/-- An effect that reaches `P` is answered at a site of `P`. -/
theorem own_site_of_reach {P : List AnySite} {x : EffectV e} (h : x.Reach P) :
    ∀ o, x.own? = some o → o.site ∈ P.map (·.2.2.site) := by
  intro o ho
  cases x with
  | request => cases ho
  | command => cases ho; exact List.mem_map.2 ⟨_, h, rfl⟩
  | query => cases ho; exact List.mem_map.2 ⟨_, h, rfl⟩

theorem toOption_reach {E : List AnyEffectSite} {ss : List AnySite} {t : Ty} {x : (Ty.option t).den}
    (h : Reach ss E (Ty.option t) x) : ∀ y ∈ (Ty.toOption x).toList, Reach ss E t y := by
  rcases x with ⟨y, ⟨⟩⟩ | z
  · intro w hw
    simp only [Ty.toOption, Option.toList, List.mem_singleton] at hw
    subst hw
    exact h.1
  · intro w hw
    simp [Ty.toOption] at hw

theorem CoOkT.any {E : List AnyEffectSite} {ss : List AnySite} {t : Ty} {x : t.den} (h : Reach ss E t x) :
    CoOkT (Co.any ss) t x := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · subst hu; intro e he; subst he
    exact CoOk.any fun y hy => own_site_of_reach (h y hy)
  · subst hu; intro e he; subst he
    exact CoOk.any fun y hy => own_site_of_reach (toOption_reach h y hy)
end

section
variable {G : List Ty} (i : Nat) (ok : Nat → Bool) (D : Defs G)

/-- The kept functions an expression writes for allowed variables, with those of every global it reads
(`Expr.reach_live`). -/
def Expr.liveAll {Γ : List Ty} {t : Ty} (e : Expr G Γ t) : List AnySite :=
  Expr.liveSites i ok D e ++ (Expr.liveGlobals i ok D e).flatMap (D.usesAt sitesC)

/-- What an effect an expression returns can be: answered at the site of a `send_command` or `send_query` whose
`on_answer` is written in place, with an input its second argument builds; else answered at any site the expression
writes. -/
def Expr.oneCo {Γ : List Ty} {t : Ty} (e : Expr G Γ t) : Co :=
  match e with
  | .call f args => if sendPrim f then
      match args.closeSiteAt? 2 with
      | some s => ⟨[(s, args.spatAt 1)], []⟩
      | none => Co.one ((e.liveAll i ok D).map (·.2.2.site))
    else Co.one ((e.liveAll i ok D).map (·.2.2.site))
  | e => Co.one ((e.liveAll i ok D).map (·.2.2.site))

/-- What the fields an expression builds hold, each one effect. -/
def Exprs.oneCos {Γ : List Ty} : {ts : List Ty} → Exprs G Γ ts → Co
  | _, .nil => Co.empty
  | _, .cons x xs => (x.oneCo i ok D).append (Exprs.oneCos xs)

mutual
/-- What the list of effects, or the optional effect, an expression returns can hold of own effects: a list or
constructor written in place holds each item or field once, a `case` or `let` over data that builds only allowed
constructors (`Expr.okIn`) holds what one live clause or its body holds, and anything else any effects of the sites it
writes. -/
def Expr.co {Γ : List Ty} {t : Ty} : Expr G Γ t → Co
  | .list items => Items.co items
  | .ctor _ es => Exprs.oneCos i ok D es
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

/-- A `send_command` or `send_query` whose `on_answer` is written in place starts an effect answered there, with an
input its second argument builds. -/
theorem send_fits {G Γ ps : List Ty} {ev : Ty} (D : Defs G) (f : Expr G Γ (.fn ps (.dsl .effect [ev])))
    (args : Exprs G Γ ps) (hs : sendPrim f = true) {s : SiteId} (hc : args.closeSiteAt? 2 = some s)
    (ρ : Ty.dens Γ) :
    ∀ o, (Expr.eval D D.eval (.call f args) ρ).own? = some o → o.site = s ∧ o.Fits (args.spatAt 1) := by
  unfold sendPrim at hs
  split at hs
  · rename_i p ts hp
    rcases Prim.sends_eq hs with rfl | rfl
    all_goals
      rcases args with _ | ⟨n, _ | ⟨x, _ | ⟨oa, _ | ⟨_, _⟩⟩⟩⟩
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
        refine ⟨rfl, fun h => ?_⟩
        simp only [Exprs.spatAt, Prim.dn, Ty.up_down]
        exact Expr.spat_fits D D.eval x ρ
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
  have hdf : CoOk (Co.one ((e.liveAll i ok D).map (·.2.2.site))) [e.eval D D.eval ρ] :=
    CoOk.one (own_site_of_reach hr)
  unfold Expr.oneCo
  split
  · rename_i f args
    split
    · rename_i hs
      split
      · rename_i s hc
        exact CoOk.send (send_fits D f args hs hc ρ)
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
  | .list items, he, ρ, hρ, hoρ => ⟨fun u hu => by
      cases hu
      exact Items.co_ok items (by simpa [Expr.effectSites] using he) ρ hρ hoρ, fun u hu => by cases hu⟩
  | @Expr.ctor _ _ j args vs v es, he, ρ, hρ, hoρ => by
    refine ⟨fun u hu => (by cases hu), fun u hu => ?_⟩
    cases hu
    simp only [Expr.co]
    match v, es with
    | ⟨0, _⟩, .cons x .nil =>
      simp only [Expr.effectSites, Exprs.effectSites] at he
      exact CoOkL.append (Expr.oneCo_ok hDE hi hok x (sub_l he) ρ hρ hoρ) CoOkL.empty
    | ⟨1, _⟩, .nil => exact CoOkL.empty
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
  | .field .., he, ρ, hρ, hoρ | .index .., he, ρ, hρ, hoρ | .update .., he, ρ, hρ, hoρ
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

section
variable {i : Nat}

mutual
/-- Every value is `Ok` where every constructor is allowed. -/
theorem ok_true : (t : Ty) → (x : t.den) → Ok i (fun _ => True) t x
  | .int, _ | .str, _ | .param _, _ | .point _, _ | .id, _ => trivial
  | .list t, _ => fun x _ => ok_true t x
  | .bag t, _ => fun x _ => ok_true t x
  | .table k w, _ => fun e _ => ⟨ok_true k e.1, ok_true w e.2⟩
  | .tuple ts, x => oks_true ts x
  | .adt _ _ vs, x => ⟨fun _ => trivial, okAlts_true vs x⟩
  | .fn _ r, f => fun xs _ => ok_true r (f xs)
  | .dsl k a, x => by
    match k, a, x with
    | .closure, [t], f => exact ok_true t _
    | .effect, [e], x =>
      match x with
      | .request _ => trivial
      | .command .. => exact fun _ _ z _ => ok_true e z
      | .query .. => exact fun _ _ z _ => ok_true e z
    | .effectClosure, [.fn _ r], _ => exact fun _ _ => ok_true r _
    | .spec, _, _ | .service, _, _ | .command, _, _ | .query, _, _ | .machine, _, _
    | .reaction, _, _ | .external, _, _ | .externalCommand, _, _ | .externalQuery, _, _
    | .source, _, _ | .declared, _, _ | .subscription, _, _ | .model, _, _ | .scope, _, _ | .values, _, _
    | .create, _, _ | .response, _, _ | .scenario, _, _ | .step, _, _ | .sender, _, _ | .fresh, _, _ => trivial
    | .closure, [], _ | .closure, _ :: _ :: _, _ | .effect, [], _ | .effect, _ :: _ :: _, _
    | .effectClosure, [], _ => trivial
    | .effectClosure, _ :: _ :: _, _ => simp [Ok]
    | .effectClosure, [.int], _ | .effectClosure, [.str], _ | .effectClosure, [.list _], _
    | .effectClosure, [.tuple _], _ | .effectClosure, [.adt ..], _ | .effectClosure, [.param _], _
    | .effectClosure, [.bag _], _ | .effectClosure, [.table ..], _ | .effectClosure, [.point _], _
    | .effectClosure, [.id], _ | .effectClosure, [.dsl ..], _ => trivial
theorem oks_true : (ts : List Ty) → (xs : Ty.dens ts) → Oks i (fun _ => True) ts xs
  | [], _ => trivial
  | t :: ts, (x, xs) => ⟨ok_true t x, oks_true ts xs⟩
theorem okAlts_true : (vs : List (List Ty)) → (x : Ty.alts vs) → OkAlts i (fun _ => True) vs x
  | [], e => nomatch e
  | fs :: _, .inl x => oks_true fs x
  | _ :: vs, .inr y => okAlts_true vs y
end

end

/-- What a function that returns effects starts for allowed arguments (`Expr.co` of a function written in place). -/
def EffectFun.co (i : Nat) (ok : Nat → Bool) {ps : List Ty} {r : Ty} (f : EffectFun ps r) : Co :=
  match f.body with
  | .lam body => body.co i ok f.defs
  | body => Co.any (body.uses sitesC f.defs)

/-- A function that returns effects starts, for allowed arguments, what `EffectFun.co` reads off it, where the values
it captured are allowed. -/
theorem EffectFun.co_ok {i : Nat} {okV : Nat → Prop} {ok : Nat → Bool} (hi : 15 ≤ i)
    (hok : ∀ k, okV k ↔ ok k = true) {P : List AnySite} {E : List AnyEffectSite} {ps : List Ty} {r : Ty}
    (f : EffectFun ps r) (hf : f.Reach P E) (henv : Oks i okV f.Γ (Ty.up _ f.hΓ f.env))
    (xs : (Ty.tuple ps).den0) (hxs : Oks i okV ps (Ty.up _ f.hps xs)) : CoOkT (f.co i ok) r (f.apply xs) := by
  have hu := hf.effectSites
  have hρ : ∀ P', Reaches P' E f.Γ (Ty.up _ f.hΓ f.env) := fun P' => reach_data P' (.tuple f.Γ) f.hΓ _
  have hps : ∀ P', Reaches P' E ps (Ty.up _ f.hps xs) := fun P' => reach_data P' (.tuple ps) f.hps _
  revert hu
  unfold EffectFun.co EffectFun.apply
  generalize f.body = body
  intro hu
  split
  · exact Expr.co_ok hf.defsEffectSites hi hok _ (by simpa [Expr.effectSites] using hu) _
      (fun P' => Dens.reach_append P' _ _ (hps P') (hρ P')) (Dens.ok_append _ _ hxs henv)
  · refine CoOkT.any (E := E) ?_
    have h : ∀ s ∈ body.uses sitesC f.defs, s ∈ body.uses sitesC f.defs := fun _ h => h
    simp only [Expr.uses, Expr.usesWith, sitesC] at h
    exact Expr.reach _ f.defs f.defs.eval (fun v h => Defs.reach _ f.defs hf.defsEffectSites v h)
      hf.defsEffectSites body (sub_l h) (fun j hj s hs => sub_r h s (List.mem_flatMap.2 ⟨j, hj, hs⟩)) hu _ (hρ _) _
      (hps _)

/-- What the reactions `ys` start for one event: each reaction's own effects (`EffectFun.co`), and any effect of one
reaction with any effect of a later one. -/
def reactionsCo (i : Nat) (ok : Nat → Bool) {r e : Ty} : List (ReactionV r e) → Co
  | [] => Co.empty
  | y :: ys => (y.react.co i ok).append (reactionsCo i ok ys)

namespace Step

/-- The waiting own effects of a step in progress: each answered at a site of `C` (whose effects a step may start any
number of, with any input) or as an item of `c` says, and two of them, where neither is answered at a site of `C`, at
a pair `c` allows. -/
def QueueCo {v : ServiceV} (C : List SiteId) (c : Co) (a : Acc v) : Prop :=
  (∀ o ∈ a.own, o.site ∈ C ∨ ∃ p, (o.site, p) ∈ c.items ∧ o.Fits p) ∧
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
    exact (EffectFun.co_ok hi hok y.react (hv.reactions y hy) (oks_free _ (hq.reactions y hy) _)
      (.inl (records, now, ()), ev, ())
      (oks_up_cons _ _ _ (fun _ => ok_free _ (by
        simp [Ty.reactionCtx, Ty.mentionsL, Ty.mentions, Ty.mentionsLL, hq.records]; omega) _)
        (fun _ => oks_up_cons _ _ _ hev (fun _ => trivial)))).1 _ rfl _ rfl

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
    rw [QueueCo, start_own_eq _ _ h1, List.nil_append]
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
    have hl : (v.reactions.flatMap fun y => (y.effectsAt ev records s.now).map (Sender.reaction y.name, ·)).map
        (·.2) = v.reactions.flatMap fun y => y.effectsAt ev records s.now := by
      simp [List.map_flatMap, Function.comp_def]
    refine ⟨fun o ho => ?_, ?_⟩
    · obtain ⟨x, hx, ho⟩ := List.mem_filterMap.1 ho
      rw [hsplit] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact .inl (hmach x hx o ho)
      · exact .inr (hre.1 x.2 (hl ▸ List.mem_map_of_mem hx) o ho)
    rw [List.pairwise_filterMap, hsplit, List.pairwise_append]
    refine ⟨List.pairwise_of_forall_mem_list fun x hx y _ o1 h1 o2 _ => .inl (hmach x hx o1 h1), ?_, ?_⟩
    · have h2 := hre.2
      rw [← hl, List.pairwise_map] at h2
      exact h2.imp fun hr o1 ho1 o2 ho2 => .inr (.inr (hr o1 o2 ho1 ho2))
    · intro x hx y _ o1 h1 o2 _
      exact .inl (hmach x hx o1 (by simpa using h1))

end

/-- What a clock line's timers start: any number of effects of every machine's `effect`, in any state, each as that
function's code builds it. -/
def _root_.Tazuna.Ir.machinesCo {r e : Ty} (ms : List (MachineV r e)) : Co :=
  let items := ms.flatMap fun m => (m.effect.co 15 (fun _ => true)).items
  ⟨items, (items.map (·.1)).flatMap fun a => (items.map (·.1)).map (a, ·)⟩

theorem effectAt_items {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E)
    {m : MachineV v.records v.event} (hm : m ∈ v.machines) (key : m.key.den0) (st : m.state.den0)
    (records : v.records.den0) (now : Int) : ∀ eff ∈ m.effectAt key st records now, ∀ o, eff.own? = some o →
      ∃ p, (o.site, p) ∈ (m.effect.co 15 (fun _ => true)).items ∧ o.Fits p := by
  intro eff heff o ho
  have h := (EffectFun.co_ok (i := 15) (okV := fun _ => True) (ok := fun _ => true) (by decide)
    (fun _ => ⟨fun _ => rfl, fun _ => trivial⟩) m.effect (hv.machines m hm).effect (oks_true _ _)
    (.inl (key, st, records, now, ()), ()) (oks_true _ _)).2 _ rfl _ rfl
  exact h.1 eff (Option.mem_toList.2 heff) o ho

/-- Every effect a clock line's timers start is an effect a machine's `effect` starts. -/
theorem fire_from (s : State v) : (fuel : Nat) → {r : State v × List (Sender × EffectV v.event)} →
    fire s fuel = some r → ∀ x ∈ r.2, ∃ m ∈ v.machines, ∃ key st records now, x.2 ∈ m.effectAt key st records now
  | 0, _, h => by cases h
  | fuel + 1, r, h => by
    rw [fire] at h
    split at h
    · cases h; intro x hx; cases hx
    · rename_i d _
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
      have h2 := fire_from { s with machines := (fireMachines s.records s.now d false s.machines).1 } fuel hr
      have hfx := mem_fireMachines_effs s.records s.now d false s.machines
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨ms, hms, k, st, hx⟩ := hfx x hx
        simp only [enter, List.mem_map, Option.mem_toList] at hx
        obtain ⟨eff, heff, rfl⟩ := hx
        exact ⟨ms.1, PerMachine.fst_mem hms, k, st, _, _, heff⟩
      · exact h2 x hx

/-- The cascade of a clock line starts with effects as `machinesCo` reads them. -/
theorem clock_queueCo {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E) {C : List SiteId}
    (s : State v) (fuel : Nat) {s' : State v} {effs : List (Sender × EffectV v.event)} (hf : fire s fuel = some (s', effs))
    {a : Acc v} (h : start { state := s' } effs = .ok a) : QueueCo C (machinesCo v.machines) a := by
  have hitems : ∀ o ∈ a.own, ∃ p, (o.site, p) ∈ (machinesCo v.machines).items ∧ o.Fits p := by
    intro o ho
    rw [start_own_eq _ _ h, List.nil_append] at ho
    obtain ⟨x, hx, ho⟩ := List.mem_filterMap.1 ho
    obtain ⟨m, hm, key, st, records, now, heff⟩ := fire_from s fuel hf x hx
    obtain ⟨p, hp, hfit⟩ := effectAt_items hv hm key st records now x.2 heff o ho
    exact ⟨p, List.mem_flatMap.2 ⟨m, hm, hp⟩, hfit⟩
  refine ⟨fun o ho => .inr (hitems o ho), List.pairwise_of_forall_mem_list fun o1 h1 o2 h2 => .inr (.inr (.inl ?_))⟩
  obtain ⟨_, hp1, -⟩ := hitems o1 h1
  obtain ⟨_, hp2, -⟩ := hitems o2 h2
  exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hp1, rfl⟩, List.mem_map.2 ⟨_, List.mem_map.2 ⟨_, hp2, rfl⟩, rfl⟩⟩

section
variable {i : Nat} {okV : Nat → Prop} {ok : Nat → Bool} {P : List AnySite} {E : List AnyEffectSite}
  (hi : 15 ≤ i) (hq : Quiet i v) (hv : v.Reach P E) (hok : ∀ k, okV k ↔ ok k = true)
include hi hq hv hok

set_option linter.unusedSectionVars false

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
    refine ⟨fun o ho => ?_, List.pairwise_append.2 ⟨ha.2.sublist (List.eraseIdx_sublist _ _),
      List.pairwise_of_forall_mem_list fun o1 h1 _ _ => .inl (hin o1 h1), fun _ _ o2 h2 => .inr (.inl (hin o2 h2))⟩⟩
    rcases List.mem_append.1 ho with ho | ho
    · exact ha.1 o (List.mem_of_mem_eraseIdx ho)
    · exact .inl (hin o ho)

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
