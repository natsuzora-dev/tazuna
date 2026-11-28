import Tazuna.Semantics.Rename

/-! Every built-in, and so every expression, preserves the renaming relation: given related arguments it gives related
results. For the bag and table built-ins this is the claim `Tazuna.Semantics.Builtin` makes in prose, that no
operation reveals the order a bag or table happens to be stored in, now a theorem (`Prim.den_rel`); for `fresh` it says
a renamed counter makes the renamed id. `Expr.eval_rel` is the fundamental lemma of the logical relation: an
expression evaluated in related environments gives related values, so every function a spec writes respects every
renaming. -/

namespace Tazuna.Ir

variable {R : PBij}

section Lemmas

mutual
theorem Ty.isData_of_comparable : (t : Ty) → t.comparable = true → t.isData = true
  | .int, _ | .str, _ | .param _, _ | .point _, _ | .id, _ => rfl
  | .list t, h | .bag t, h => Ty.isData_of_comparable t h
  | .table k v, h => by
    simp only [Ty.comparable, Bool.and_eq_true] at h
    simp only [Ty.isData, Bool.and_eq_true]
    exact ⟨Ty.isData_of_comparable k h.1, Ty.isData_of_comparable v h.2⟩
  | .tuple ts, h => Ty.isDatas_of_comparables ts h
  | .adt _ _ vs, h => Ty.isDatass_of_comparabless vs h
  | .fn .., h => by simp [Ty.comparable] at h
  | .dsl _ _, h => h
theorem Ty.isDatas_of_comparables : (ts : List Ty) → Ty.comparables ts = true → Ty.isDatas ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.comparables, Bool.and_eq_true] at h
    simp only [Ty.isDatas, Bool.and_eq_true]
    exact ⟨Ty.isData_of_comparable t h.1, Ty.isDatas_of_comparables ts h.2⟩
theorem Ty.isDatass_of_comparabless : (vs : List (List Ty)) → Ty.comparabless vs = true → Ty.isDatass vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at h
    simp only [Ty.isDatass, Bool.and_eq_true]
    exact ⟨Ty.isDatas_of_comparables ts h.1, Ty.isDatass_of_comparabless vs h.2⟩
end

theorem Ty.rel0_down {t : Ty} (h : t.isData = true) {x y : t.den} (hxy : Ty.relV R t x y) :
    Ty.rel0 R t (Ty.down t h x) (Ty.down t h y) :=
  (Ty.relV_up t h _ _).1 (by rw [Ty.up_down, Ty.up_down]; exact hxy)

theorem Ty.relV_up_of {t : Ty} (h : t.isData = true) {x y : t.den0} (hxy : Ty.rel0 R t x y) :
    Ty.relV R t (Ty.up t h x) (Ty.up t h y) :=
  (Ty.relV_up t h _ _).2 hxy

/-- `==` on a data value is `==` on it as data. -/
theorem Ty.deq_down {t : Ty} (h : t.isData = true) (x y : t.den) : Ty.deq t x y = Ty.deq0 t (Ty.down t h x) (Ty.down t h y) := by
  conv => lhs; rw [← Ty.up_down t h x, ← Ty.up_down t h y]
  exact Ty.deq_up t h _ _

theorem Ty.relV_deq {t : Ty} (hc : t.comparable = true) {x y x' y' : t.den} (h : Ty.relV R t x y)
    (h' : Ty.relV R t x' y') : Ty.deq t x x' = Ty.deq t y y' := by
  have hd := Ty.isData_of_comparable t hc
  rw [Ty.deq_down hd, Ty.deq_down hd]
  exact Ty.rel0_deq t hc (Ty.rel0_down hd h) (Ty.rel0_down hd h')

theorem Ty.deq_symm {t : Ty} (hc : t.comparable = true) {x y : t.den} (e : Ty.deq t x y = true) : Ty.deq t y x = true := by
  have hd := Ty.isData_of_comparable t hc
  rw [Ty.deq_down hd] at e ⊢
  exact Ty.deq0_symm hc e

theorem Ty.deq_trans {t : Ty} (hc : t.comparable = true) {x y z : t.den} (e : Ty.deq t x y = true)
    (e' : Ty.deq t y z = true) : Ty.deq t x z = true := by
  have hd := Ty.isData_of_comparable t hc
  rw [Ty.deq_down hd] at e e' ⊢
  exact Ty.deq0_trans hc e e'

theorem Ty.relV_bool {a b : Ty.bool.den} (h : Ty.relV R Ty.bool a b) : Ty.toBool a = Ty.toBool b := by
  match a, b, h with
  | .inl _, .inl _, _ => rfl
  | .inr _, .inr _, _ => rfl

theorem Ty.relV_ofBool (x : Bool) : Ty.relV R Ty.bool (Ty.ofBool x) (Ty.ofBool x) := by
  cases x <;> exact ⟨⟩

theorem Ty.relV_ofBool_eq {x y : Bool} (h : x = y) : Ty.relV R Ty.bool (Ty.ofBool x) (Ty.ofBool y) :=
  h ▸ Ty.relV_ofBool x

theorem Multi.eq_perm {α : Type} {xs ys : List α} : Multi (· = ·) xs ys → xs.Perm ys
  | ⟨zs, h, hz⟩ => by
    have : xs = zs := by
      clear hz
      induction xs generalizing zs with
      | nil => cases zs <;> simp_all [Forall2]
      | cons x xs ih =>
        cases zs with
        | nil => exact h.elim
        | cons z zs => obtain ⟨rfl, h⟩ := h; rw [ih zs h]
    exact this ▸ hz

theorem sumBy_multi {α β : Type} {r : α → β → Prop} {f : α → Int} {g : β → Int} (hfg : ∀ a b, r a b → f a = g b)
    {xs : List α} {ys : List β} (h : Multi r xs ys) : Builtin.sumBy f xs = Builtin.sumBy g ys := by
  unfold Builtin.sumBy
  rw [(Multi.eq_perm (h.map (r' := (· = ·)) hfg)).foldl_eq' (fun _ _ _ _ _ => by omega)]

theorem foldl_rel {α β γ δ : Type} {r : α → β → Prop} {s : γ → δ → Prop} {f : γ → α → γ} {g : δ → β → δ}
    (hfg : ∀ c d a b, s c d → r a b → s (f c a) (g d b)) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → {c : γ} → {d : δ} → s c d → s (xs.foldl f c) (ys.foldl g d)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, ⟨hab, hr⟩, _, _, h => foldl_rel hfg hr (hfg _ _ _ _ h hab)
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

theorem Multi.singleton {α β : Type} {r : α → β → Prop} {a : α} {ys : List β} (h : Multi r [a] ys) :
    ∃ b, ys = [b] ∧ r a b := by
  obtain ⟨zs, h, hz⟩ := h
  match zs, h with
  | [b], ⟨hab, _⟩ => exact ⟨b, (List.perm_singleton.1 hz.symm), hab⟩

end Lemmas

section Pick

/-- The fold `pick` takes its best key with: a minimum or a maximum. -/
theorem foldl_best_perm {op : Int → Int → Int} (hc : ∀ a b, op a b = op b a) (ha : ∀ a b c, op (op a b) c = op a (op b c))
    {x y : Int} {l l' : List Int} (hp : (x :: l).Perm (y :: l')) :
    l.foldl (fun m k => op k m) x = l'.foldl (fun m k => op k m) y := by
  have rc : ∀ (L : List Int), ∀ a ∈ L, ∀ b ∈ L, ∀ z, op b (op a z) = op a (op b z) :=
    fun _ a _ b _ z => by rw [← ha, hc b a, ha]
  have perm : ∀ {L L' : List Int}, L.Perm L' → ∀ z, L.foldl (fun m k => op k m) z = L'.foldl (fun m k => op k m) z :=
    fun hL z => hL.foldl_eq' (fun a ha b hb z => rc _ a ha b hb z) z
  by_cases hxy : x = y
  · subst hxy; exact perm (List.perm_cons x |>.1 hp) x
  · have hy : y ∈ l := by
      have := hp.mem_iff.2 List.mem_cons_self
      rcases List.mem_cons.1 this with h | h
      · exact absurd h.symm hxy
      · exact h
    have hl : l.Perm (y :: l.erase y) := List.perm_cons_erase hy
    have hl' : l'.Perm (x :: l.erase y) :=
      (List.perm_cons y).1 (hp.symm.trans ((hl.cons x).trans (List.Perm.swap y x _)))
    rw [perm hl x, perm hl' y]
    simp only [List.foldl_cons, hc]

theorem pick_multi {α β : Type} {r : α → β → Prop} {wins : Int → Int → Bool} {op : Int → Int → Int}
    (hop : ∀ m y, (if wins y m then y else m) = op y m) (hc : ∀ a b, op a b = op b a)
    (ha : ∀ a b c, op (op a b) c = op a (op b c)) {key : α → Int} {key' : β → Int}
    (hk : ∀ a b, r a b → key a = key' b) {xs : List α} {ys : List β} (h : Multi r xs ys) :
    (∃ e, Builtin.pick wins key xs = .error e ∧ Builtin.pick wins key' ys = .error e) ∨
      ∃ a b, Builtin.pick wins key xs = .ok a ∧ Builtin.pick wins key' ys = .ok b ∧ r a b := by
  match xs, ys, h.length_eq with
  | [], [], _ => exact .inl ⟨false, rfl, rfl⟩
  | x :: rest, y :: rest', _ =>
    have hb : rest.foldl (fun m z => if wins (key z) m then key z else m) (key x) =
        rest'.foldl (fun m z => if wins (key' z) m then key' z else m) (key' y) := by
      have e1 : rest.foldl (fun m z => if wins (key z) m then key z else m) (key x) =
          (rest.map key).foldl (fun m k => op k m) (key x) := by rw [List.foldl_map]; simp only [hop]
      have e2 : rest'.foldl (fun m z => if wins (key' z) m then key' z else m) (key' y) =
          (rest'.map key').foldl (fun m k => op k m) (key' y) := by rw [List.foldl_map]; simp only [hop]
      rw [e1, e2]
      exact foldl_best_perm hc ha (Multi.eq_perm (h.map (r' := (· = ·)) hk))
    unfold Builtin.pick
    simp only
    rw [hb]
    have hf := h.filter (p := (key · == rest'.foldl (fun m z => if wins (key' z) m then key' z else m) (key' y)))
      (q := (key' · == rest'.foldl (fun m z => if wins (key' z) m then key' z else m) (key' y)))
      (fun a b hab => by rw [hk a b hab])
    generalize (x :: rest).filter _ = l at hf
    generalize (y :: rest').filter _ = l' at hf
    match l, l' with
    | [a], l' =>
      obtain ⟨b, rfl, hab⟩ := hf.singleton
      exact .inr ⟨a, b, rfl, rfl, hab⟩
    | l, [b] =>
      obtain ⟨a, rfl, hab⟩ := hf.flip.singleton
      exact .inr ⟨a, b, rfl, rfl, hab⟩
    | [], [] => exact .inl ⟨true, rfl, rfl⟩
    | [], _ :: _ :: _ | _ :: _ :: _, [] => exact absurd hf.length_eq (by simp)
    | _ :: _ :: _, _ :: _ :: _ => exact .inl ⟨true, rfl, rfl⟩

theorem ofPick_rel {a : Ty} {x y : Except Bool a.den}
    (h : (∃ e, x = .error e ∧ y = .error e) ∨ ∃ u v, x = .ok u ∧ y = .ok v ∧ Ty.relV R a u v) :
    Ty.relV R (Ty.result a .pickError) (Ty.ofPick x) (Ty.ofPick y) := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨u, v, rfl, rfl, huv⟩
  · cases e <;> exact ⟨trivial, trivial⟩
  · exact ⟨huv, trivial⟩

end Pick

section Table
variable {K V : Ty}

theorem tableInsert_rel (hK : K.comparable = true) {t t' : (Ty.table K V).den} {k k' : K.den} {v v' : V.den}
    (ht : Ty.relV R (.table K V) t t') (hk : Ty.relV R K k k') (hv : Ty.relV R V v v') :
    Ty.relV R (.table K V) (Builtin.tableInsert k v t) (Builtin.tableInsert k' v' t') := by
  show Multi _ ((Builtin.tableRemove k t).1 ++ [(k, v)]) ((Builtin.tableRemove k' t').1 ++ [(k', v')])
  refine Multi.append (Multi.filter (fun a b hab => ?_) ht) (Multi.cons ⟨hk, hv⟩ Multi.nil)
  simp only [Builtin.sameKey, Ty.relV_deq hK hk hab.1, Ty.relV_deq hK hab.1 hk]

theorem tableRemove_rel (hK : K.comparable = true) {t t' : (Ty.table K V).den} {k k' : K.den}
    (ht : Ty.relV R (.table K V) t t') (hk : Ty.relV R K k k') :
    Ty.relV R (.table K V) (Builtin.tableRemove k t) (Builtin.tableRemove k' t') :=
  Multi.filter (fun a b hab => by simp only [Builtin.sameKey, Ty.relV_deq hK hk hab.1, Ty.relV_deq hK hab.1 hk]) ht

theorem lookup_rel (hK : K.comparable = true) {t t' : (Ty.table K V).den} {k k' : K.den}
    (ht : Ty.relV R (.table K V) t t') (hk : Ty.relV R K k k') :
    Option.Rel (Ty.relV R V) (lookupBy (Ty.deq K) k t.1) (lookupBy (Ty.deq K) k' t'.1) := by
  obtain ⟨zs, h, hz⟩ := ht
  have := lookupBy_forall2 (fk := Ty.deq K) (gk := Ty.deq K) (rv := Ty.relV R V)
    (fun _ _ _ _ => Ty.relV_deq hK) hk h
  rwa [lookupBy_perm (fk := Ty.deq K) (fun _ _ => Ty.deq_symm hK) (fun _ _ _ => Ty.deq_trans hK) (keysUnique_perm hz.symm t'.2) hz]
    at this

end Table

theorem Prim.comparable0 {p : Prim} {args : List Ty} (h : p.ok args = true) (hp : p.sig.needsEq = [0]) :
    ((Ty.param 0).inst args).comparable = true := by
  simp only [Prim.ok, hp, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have := h.1.2
  simp only [Ty.inst]
  cases e : args[0]? with
  | none => rw [e] at this; cases this
  | some t => rw [e] at this; simpa using this

/-- Services whose lists relate, with the same parts once `spec`'s additions are set aside, keep parts related to
themselves. -/
theorem Self.of_stripped {vs ws : List ServiceV}
    (h : Forall2 (fun v w => ServiceV.stripped v = ServiceV.stripped w → ServiceV.Self R v) vs ws)
    (he : vs.map ServiceV.stripped = ws.map ServiceV.stripped) : ∀ v ∈ vs, ServiceV.Self R v := by
  induction vs generalizing ws with
  | nil => intro _ hv; nomatch hv
  | cons v vs ih =>
    cases ws with
    | nil => exact h.elim
    | cons w ws =>
      simp only [List.map_cons, List.cons.injEq] at he
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1 he.1
      · exact ih h.2 he.2 x hx

/-- Items that are the same once stripped relate to themselves where the relation says so. -/
theorem self_of_map {α : Type} {c : α → α} {P : α → Prop} {xs ys : List α}
    (h : Forall2 (fun x y => c x = c y → P x) xs ys) (he : xs.map c = ys.map c) : ∀ x ∈ xs, P x := by
  induction xs generalizing ys with
  | nil => intro _ hx; nomatch hx
  | cons x xs ih =>
    cases ys with
    | nil => exact h.elim
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at he
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h.1 he.1
      · exact ih h.2 he.2 z hz

theorem map_stripped (f : ServiceV → ServiceV) (hf : ∀ v, (f v).stripped = v.stripped) :
    (l : List ServiceV) → (l.map f).map ServiceV.stripped = l.map ServiceV.stripped
  | [] => rfl
  | v :: l => by simp only [List.map_cons, hf, map_stripped f hf l]

theorem stripped_of_map {f g : ServiceV → ServiceV} {l l' : List ServiceV}
    (hf : ∀ v, (f v).stripped = v.stripped) (hg : ∀ v, (g v).stripped = v.stripped)
    (h : (l.map f).map ServiceV.stripped = (l'.map g).map ServiceV.stripped) :
    l.map ServiceV.stripped = l'.map ServiceV.stripped :=
  (map_stripped f hf l).symm.trans (h.trans (map_stripped g hg l'))

theorem Self.commands_of {r e c : Ty} {ds : List DeclaredV} (h : ∀ d ∈ ds, d = d → DeclaredV.Self R d) :
    ∀ x ∈ ds.filterMap (fun
      | .command r' e' c' x => match Ty.same r' r, Ty.same e' e, Ty.same c' c with
        | some ⟨h1⟩, some ⟨h2⟩, some ⟨h3⟩ => some (h1 ▸ h2 ▸ h3 ▸ x)
        | _, _, _ => none
      | _ => none), CommandV.Self R x := by
  intro x hx
  obtain ⟨d, hd, hdx⟩ := List.mem_filterMap.1 hx
  have hs := h d hd rfl
  match d, hdx, hs with
  | .command r' e' c' y, hdx, hs =>
    revert hdx
    dsimp only
    split
    · next h1 h2 h3 _ _ _ =>
      obtain ⟨⟩ := h1; obtain ⟨⟩ := h2; obtain ⟨⟩ := h3
      intro hdx; cases hdx; exact hs
    · intro hdx; cases hdx

theorem Self.queries_of {r c : Ty} {ds : List DeclaredV} (h : ∀ d ∈ ds, d = d → DeclaredV.Self R d) :
    ∀ x ∈ ds.filterMap (fun
      | .query r' c' x => match Ty.same r' r, Ty.same c' c with
        | some ⟨h1⟩, some ⟨h2⟩ => some (h1 ▸ h2 ▸ x)
        | _, _ => none
      | _ => none), QueryV.Self R x := by
  intro x hx
  obtain ⟨d, hd, hdx⟩ := List.mem_filterMap.1 hx
  have hs := h d hd rfl
  match d, hdx, hs with
  | .query r' c' y, hdx, hs =>
    revert hdx
    dsimp only
    split
    · next h1 h2 _ _ =>
      obtain ⟨⟩ := h1; obtain ⟨⟩ := h2
      intro hdx; cases hdx; exact hs
    · intro hdx; cases hdx

theorem Prim.den_rel (p : Prim) (args : List Ty) (h : p.ok args = true) :
    Ty.relV R (p.ty.inst args) (p.den args h) (p.den args h) := by
  cases p with
  | length => rintro ⟨s, ⟨⟩⟩ ⟨s', ⟨⟩⟩ ⟨hs, -⟩; exact congrArg (Gleam.length ∘ Subtype.val) hs
  | bagFromList => rintro ⟨xs, ⟨⟩⟩ ⟨ys, ⟨⟩⟩ ⟨hxs, -⟩; exact Multi.of_forall2 hxs
  | bagInsert => rintro ⟨xs, x, ⟨⟩⟩ ⟨ys, y, ⟨⟩⟩ ⟨hxs, hx, -⟩; exact Multi.cons hx hxs
  | bagSize => rintro ⟨xs, ⟨⟩⟩ ⟨ys, ⟨⟩⟩ ⟨hxs, -⟩; exact congrArg (fun n : Nat => (n : Int)) hxs.length_eq
  | bagFilter =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    exact Multi.filter (fun x y hxy => Ty.relV_bool (hf (x, ()) (y, ()) ⟨hxy, trivial⟩)) hxs
  | bagMap =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    exact Multi.map (fun x y hxy => hf (x, ()) (y, ()) ⟨hxy, trivial⟩) hxs
  | bagCount =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    exact congrArg (fun n : Nat => (n : Int))
      (Multi.filter (fun x y hxy => Ty.relV_bool (hf (x, ()) (y, ()) ⟨hxy, trivial⟩)) hxs).length_eq
  | bagSum =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    exact sumBy_multi (fun x y hxy => hf (x, ()) (y, ()) ⟨hxy, trivial⟩) hxs
  | bagAny =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    show Ty.relV R Ty.bool (Ty.ofBool _) (Ty.ofBool _)
    rw [hxs.any_eq (fun x y hxy => Ty.relV_bool (hf (x, ()) (y, ()) ⟨hxy, trivial⟩))]
    exact Ty.relV_ofBool _
  | bagAll =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    show Ty.relV R Ty.bool (Ty.ofBool _) (Ty.ofBool _)
    rw [hxs.all_eq (fun x y hxy => Ty.relV_bool (hf (x, ()) (y, ()) ⟨hxy, trivial⟩))]
    exact Ty.relV_ofBool _
  | bagContains =>
    rintro ⟨xs, x, ⟨⟩⟩ ⟨ys, y, ⟨⟩⟩ ⟨hxs, hx, -⟩
    exact Ty.relV_ofBool_eq (hxs.any_eq (fun a b hab => Ty.relV_deq (Prim.comparable0 h rfl) hx hab))
  | bagMinBy =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    exact ofPick_rel (pick_multi (op := min) (fun m y => by simp only [Int.min_def, decide_eq_true_eq]; split <;> split <;> omega)
      Int.min_comm Int.min_assoc (fun x y hxy => hf (x, ()) (y, ()) ⟨hxy, trivial⟩) hxs)
  | bagMaxBy =>
    rintro ⟨xs, f, ⟨⟩⟩ ⟨ys, g, ⟨⟩⟩ ⟨hxs, hf, -⟩
    exact ofPick_rel (pick_multi (op := max) (fun m y => by simp only [Int.max_def, decide_eq_true_eq]; split <;> split <;> omega)
      Int.max_comm Int.max_assoc (fun x y hxy => hf (x, ()) (y, ()) ⟨hxy, trivial⟩) hxs)
  | tableNew => intro _ _ _; exact Multi.nil
  | tableFromList =>
    rintro ⟨ps, ⟨⟩⟩ ⟨ps', ⟨⟩⟩ ⟨hps, -⟩
    refine foldl_rel (fun t t' kv kv' ht hkv => ?_) hps Multi.nil
    obtain ⟨k, v, ⟨⟩⟩ := kv
    obtain ⟨k', v', ⟨⟩⟩ := kv'
    exact tableInsert_rel (Prim.comparable0 h rfl) ht hkv.1 hkv.2.1
  | tableInsert =>
    rintro ⟨t, k, v, ⟨⟩⟩ ⟨t', k', v', ⟨⟩⟩ ⟨ht, hk, hv, -⟩
    exact tableInsert_rel (Prim.comparable0 h rfl) ht hk hv
  | tableRemove =>
    rintro ⟨t, k, ⟨⟩⟩ ⟨t', k', ⟨⟩⟩ ⟨ht, hk, -⟩
    exact tableRemove_rel (Prim.comparable0 h rfl) ht hk
  | tableGet =>
    rintro ⟨t, k, ⟨⟩⟩ ⟨t', k', ⟨⟩⟩ ⟨ht, hk, -⟩
    have := lookup_rel (Prim.comparable0 h rfl) ht hk
    show Ty.relV R _ (match lookupBy (Ty.deq ((Ty.param 0).inst args)) k t.1 with | .some v => Ty.some v | .none => Ty.none)
      (match lookupBy (Ty.deq ((Ty.param 0).inst args)) k' t'.1 with | .some v => Ty.some v | .none => Ty.none)
    revert this
    cases lookupBy (Ty.deq ((Ty.param 0).inst args)) k t.1 <;>
      cases lookupBy (Ty.deq ((Ty.param 0).inst args)) k' t'.1 <;> intro hr <;> cases hr
    · exact ⟨⟩
    · exact ⟨by assumption, trivial⟩
  | tableSize => rintro ⟨t, ⟨⟩⟩ ⟨t', ⟨⟩⟩ ⟨ht, -⟩; exact congrArg (fun n : Nat => (n : Int)) (Multi.length_eq ht)
  | tableKeys => rintro ⟨t, ⟨⟩⟩ ⟨t', ⟨⟩⟩ ⟨ht, -⟩; exact Multi.map (fun _ _ h => h.1) ht
  | tableValues => rintro ⟨t, ⟨⟩⟩ ⟨t', ⟨⟩⟩ ⟨ht, -⟩; exact Multi.map (fun _ _ h => h.2) ht
  | tableFilter =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨t', g, ⟨⟩⟩ ⟨ht, hf, -⟩
    exact Multi.filter (fun a b hab => Ty.relV_bool (hf (a.1, a.2, ()) (b.1, b.2, ()) ⟨hab.1, hab.2, trivial⟩)) ht
  | tableMap =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨t', g, ⟨⟩⟩ ⟨ht, hf, -⟩
    exact Multi.map (fun a b hab => ⟨hab.1, hf (a.1, a.2, ()) (b.1, b.2, ()) ⟨hab.1, hab.2, trivial⟩⟩) ht
  | tableCount =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨t', g, ⟨⟩⟩ ⟨ht, hf, -⟩
    exact congrArg (fun n : Nat => (n : Int)) (Multi.filter (p := fun (k, v) => Ty.toBool (f (k, v, ())))
      (q := fun (k, v) => Ty.toBool (g (k, v, ())))
      (fun a b hab => Ty.relV_bool (hf (a.1, a.2, ()) (b.1, b.2, ()) ⟨hab.1, hab.2, trivial⟩)) ht).length_eq
  | tableAny =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨t', g, ⟨⟩⟩ ⟨ht, hf, -⟩
    exact Ty.relV_ofBool_eq (Multi.any_eq (p := fun (k, v) => Ty.toBool (f (k, v, ())))
      (q := fun (k, v) => Ty.toBool (g (k, v, ())))
      (fun a b hab => Ty.relV_bool (hf (a.1, a.2, ()) (b.1, b.2, ()) ⟨hab.1, hab.2, trivial⟩)) ht)
  | tableAll =>
    rintro ⟨t, f, ⟨⟩⟩ ⟨t', g, ⟨⟩⟩ ⟨ht, hf, -⟩
    exact Ty.relV_ofBool_eq (Multi.all_eq (p := fun (k, v) => Ty.toBool (f (k, v, ())))
      (q := fun (k, v) => Ty.toBool (g (k, v, ())))
      (fun a b hab => Ty.relV_bool (hf (a.1, a.2, ()) (b.1, b.2, ()) ⟨hab.1, hab.2, trivial⟩)) ht)
  | dateAddDays =>
    rintro ⟨d, n, ⟨⟩⟩ ⟨d', n', ⟨⟩⟩ ⟨hd, hn, -⟩
    show @HAdd.hAdd Int Int Int _ d n = @HAdd.hAdd Int Int Int _ d' n'
    rw [show d = d' from hd, show n = n' from hn]
  | dateDaysBetween =>
    rintro ⟨a, b, ⟨⟩⟩ ⟨a', b', ⟨⟩⟩ ⟨ha, hb, -⟩
    show @HSub.hSub Int Int Int _ b a = @HSub.hSub Int Int Int _ b' a'
    rw [show a = a' from ha, show b = b' from hb]
  | instantAdd =>
    rintro ⟨d, n, ⟨⟩⟩ ⟨d', n', ⟨⟩⟩ ⟨hd, hn, -⟩
    show @HAdd.hAdd Int Int Int _ d n = @HAdd.hAdd Int Int Int _ d' n'
    rw [show d = d' from hd, show n = n' from hn]
  | instantDiff =>
    rintro ⟨a, b, ⟨⟩⟩ ⟨a', b', ⟨⟩⟩ ⟨ha, hb, -⟩
    show @HSub.hSub Int Int Int _ b a = @HSub.hSub Int Int Int _ b' a'
    rw [show a = a' from ha, show b = b' from hb]
  | instantIsBefore | instantIsAfter =>
    rintro ⟨a, b, ⟨⟩⟩ ⟨a', b', ⟨⟩⟩ ⟨ha, hb, -⟩
    obtain rfl : a = a' := ha
    obtain rfl : b = b' := hb
    exact Ty.relV_ofBool_eq rfl
  | require =>
    rintro ⟨c, j, f, ⟨⟩⟩ ⟨c', j', g, ⟨⟩⟩ ⟨hc, hj, hf, -⟩
    show Ty.relV R _ (if Ty.toBool c then f () else Ty.error j) (if Ty.toBool c' then g () else Ty.error j')
    rw [Ty.relV_bool hc]
    cases Ty.toBool c'
    · exact ⟨hj, trivial⟩
    · exact hf () () trivial
  | tableLookup =>
    rintro ⟨t, k, j, f, ⟨⟩⟩ ⟨t', k', j', g, ⟨⟩⟩ ⟨ht, hk, hj, hf, -⟩
    have := lookup_rel (Prim.comparable0 h rfl) ht hk
    show Ty.relV R _ (match lookupBy (Ty.deq ((Ty.param 0).inst args)) k t.1 with
        | .some v => f (v, ()) | .none => Ty.error j)
      (match lookupBy (Ty.deq ((Ty.param 0).inst args)) k' t'.1 with | .some v => g (v, ()) | .none => Ty.error j')
    revert this
    cases lookupBy (Ty.deq ((Ty.param 0).inst args)) k t.1 <;>
      cases lookupBy (Ty.deq ((Ty.param 0).inst args)) k' t'.1 <;> intro hr <;> cases hr
    · exact ⟨hj, trivial⟩
    · exact hf _ _ ⟨by assumption, trivial⟩
  | fresh =>
    rintro ⟨s, i, ⟨⟩⟩ ⟨s', i', ⟨⟩⟩ ⟨hs, hi, -⟩
    obtain rfl : i = i' := hi
    exact .inr ⟨s, s', i, hs, rfl, rfl⟩
  | command =>
    rintro ⟨n, cl, acc, dec, ens, ⟨⟩⟩ ⟨n', cl', acc', dec', ens', ⟨⟩⟩ ⟨hn, hcl, hacc, hdec, hens, -⟩
    refine ⟨congrArg Subtype.val hn, fun he => ?_⟩
    simp only [Prim.den] at he
    obtain ⟨-, -, -, hcl', hacc', hdec', hens'⟩ := CommandV.mk.inj (congrArg Subtype.val he)
    dsimp only at hcl' hacc' hdec' hens'
    cases eq_of_heq hacc'; cases eq_of_heq hdec'; cases eq_of_heq hens'
    have hc := Ty.rel0_down (Ty.isData_inst (Prim.dataOf h rfl) (.list (.origin (.param 2))) rfl) hcl
    exact ⟨(congrArg (Ty.rel0 R _ _) hcl').mpr hc, hacc, hdec, hens⟩
  | query =>
    rintro ⟨n, cl, acc, res, ⟨⟩⟩ ⟨n', cl', acc', res', ⟨⟩⟩ ⟨hn, hcl, hacc, hres, -⟩
    refine ⟨congrArg Subtype.val hn, fun he => ?_⟩
    simp only [Prim.den] at he
    obtain ⟨-, -, -, hcl', hacc', hres'⟩ := QueryV.mk.inj (congrArg Subtype.val he)
    dsimp only at hcl' hacc' hres'
    cases eq_of_heq hacc'; cases eq_of_heq hres'
    have hc := Ty.rel0_down (Ty.isData_inst (Prim.dataOf h rfl) (.list (.origin (.param 1))) rfl) hcl
    exact ⟨(congrArg (Ty.rel0 R _ _) hcl').mpr hc, hacc, hres⟩
  | machine =>
    rintro ⟨n, ins, ini, on, aft, eff, inv, ⟨⟩⟩ ⟨n', ins', ini', on', aft', eff', inv', ⟨⟩⟩
      ⟨hn, hins, hini, hon, haft, heff, hinv, -⟩
    refine ⟨congrArg Subtype.val hn, fun he => ?_⟩
    simp only [Prim.den] at he
    obtain ⟨-, -, -, hins', hini', hon', haft', heff', hinv'⟩ := MachineV.mk.inj he
    cases eq_of_heq hins'; cases eq_of_heq hon'; cases eq_of_heq haft'; cases eq_of_heq heff'; cases eq_of_heq hinv'
    have hi := Ty.rel0_down (Ty.isData_inst (Prim.dataOf h rfl) (.param 3) rfl) hini
    exact ⟨hins, hon, haft, (congrArg (Ty.rel0 R _ _) (eq_of_heq hini')).mpr hi, heff rfl, hinv⟩
  | reaction =>
    rintro ⟨n, x, ⟨⟩⟩ ⟨n', x', ⟨⟩⟩ ⟨hn, hx, -⟩
    refine ⟨congrArg Subtype.val hn, fun h => ?_⟩
    simp only [Prim.den] at h
    obtain ⟨-, hx'⟩ := ReactionV.mk.inj h
    exact hx hx'
  | declareCommand =>
    rintro ⟨x, ⟨⟩⟩ ⟨x', ⟨⟩⟩ ⟨hx, -⟩ h
    simp only [Prim.den] at h
    obtain ⟨-, -, -, h⟩ := DeclaredV.command.inj h
    exact hx.2 (Subtype.ext (eq_of_heq h))
  | declareQuery =>
    rintro ⟨x, ⟨⟩⟩ ⟨x', ⟨⟩⟩ ⟨hx, -⟩ h
    simp only [Prim.den] at h
    obtain ⟨-, -, h⟩ := DeclaredV.query.inj h
    exact hx.2 (Subtype.ext (eq_of_heq h))
  | declareSource | declareExternalCommand | declareExternalQuery => intro _ _ _ _; trivial
  | spec =>
    rintro ⟨vs, xs, ⟨⟩⟩ ⟨vs', xs', ⟨⟩⟩ ⟨hvs, -, -⟩ h
    simp only [Prim.den] at h
    have hm := congrArg (List.map ServiceV.stripped) (SpecV.mk.inj h).1
    replace hm := stripped_of_map (fun _ => by simp [ServiceV.stripped, SubscriptionV.stripped, Function.comp_def])
      (fun _ => by simp [ServiceV.stripped, SubscriptionV.stripped, Function.comp_def]) hm
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    have hs := Self.of_stripped hvs hm w hw
    refine ⟨hs.init, hs.apply, fun s hs' => ?_, hs.commands, hs.queries, hs.machines, hs.reactions, hs.invariants⟩
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs'
    exact hs.subscribes s0 hs0
  | model =>
    rintro ⟨sp, scs, rl, ⟨⟩⟩ ⟨sp', scs', rl', ⟨⟩⟩ ⟨hsp, -, -, -⟩ h
    simp only [Prim.den] at h
    obtain ⟨rfl, rfl, -⟩ := ModelV.mk.inj h
    have hs := hsp rfl
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    split
    · exact ScopeV.apply_self (hs w hw)
    · exact hs w hw
  | service =>
    rintro ⟨n, ini, app, subs, ds, ms, xs, inv, rsp, bnd, scs, ⟨⟩⟩
      ⟨n', ini', app', subs', ds', ms', xs', inv', rsp', bnd', scs', ⟨⟩⟩
      ⟨-, hini, happ, hsubs, hds, hms, hxs, hinv, -⟩ h
    simp only [ServiceV.stripped, ServiceV.mk.injEq] at h
    obtain ⟨-, -, -, -, hini', rfl, hsubs', rfl, -, -, -, rfl, rfl, rfl, -⟩ := h
    have hi := Ty.rel0_down (Ty.isData_inst (Prim.dataOf h rfl) (.param 0) rfl) hini
    exact ⟨(congrArg (Ty.rel0 R _ _) (eq_of_heq hini')).mpr hi, happ, self_of_map hsubs (eq_of_heq hsubs'),
      Self.commands_of (forall2_self hds), Self.queries_of (forall2_self hds),
      fun m hm => (forall2_self hms m hm).2 rfl, fun x hx => (forall2_self hxs x hx).2 rfl, hinv⟩
  | subscribe =>
    rintro ⟨n, w, ⟨⟩⟩ ⟨n', w', ⟨⟩⟩ ⟨-, hw, -⟩ h
    simp only [Prim.den, SubscriptionV.stripped] at h
    obtain ⟨-, -, -, hw'⟩ := SubscriptionV.mk.inj h
    cases eq_of_heq hw'
    exact hw
  | externalCommand => rintro ⟨n, _⟩ ⟨n', _⟩ ⟨hn, -⟩; exact congrArg Subtype.val hn
  | externalQuery => rintro ⟨n, f, _⟩ ⟨n', f', _⟩ ⟨hn, hf, -⟩; exact ⟨congrArg Subtype.val hn, hf⟩
  | source => rintro ⟨n, _⟩ ⟨n', _⟩ ⟨hn, -⟩; exact congrArg Subtype.val hn
  | requestCommand =>
    rintro ⟨n, x, f, ⟨⟩⟩ ⟨n', x', f', ⟨⟩⟩ ⟨hn, hx, hf, -⟩
    obtain rfl : n = n' := hn
    exact .request (.mk _ _ _ _ (Ty.rel0_down _ hx) .none hf)
  | requestQuery =>
    rintro ⟨⟨n, e⟩, x, f, ⟨⟩⟩ ⟨⟨n', e'⟩, x', f', ⟨⟩⟩ ⟨⟨hn, he⟩, hx, hf, -⟩
    obtain rfl : n = n' := hn
    exact .request (.mk _ _ _ _ (Ty.rel0_down _ hx) (.some he) hf)
  | sendCommand =>
    rintro ⟨c, x, f, ⟨⟩⟩ ⟨c', x', f', ⟨⟩⟩ ⟨hc, hx, hf, -⟩
    have hc : c.1.name = c'.1.name := hc.1
    show EffectV.Rel R (.command c.1.name _ _ _ _ _) (.command c'.1.name _ _ _ _ _)
    rw [hc]
    exact .command _ _ _ _ (Ty.rel0_down _ hx) hf
  | sendQuery =>
    rintro ⟨c, x, f, ⟨⟩⟩ ⟨c', x', f', ⟨⟩⟩ ⟨hc, hx, hf, -⟩
    have hc : c.1.name = c'.1.name := hc.1
    show EffectV.Rel R (.query c.1.name _ _ _ _ _) (.query c'.1.name _ _ _ _ _)
    rw [hc]
    exact .query _ _ _ _ (Ty.rel0_down _ hx) hf
  | fromMachine =>
    rintro ⟨m, k, ⟨⟩⟩ ⟨m', k', ⟨⟩⟩ ⟨hm, hk, -⟩
    have hm : m.name = m'.name := hm.1
    show Sender.Rel R (.machine m.name _) (.machine m'.name _)
    rw [hm]
    exact .machine _ (.mk (Ty.rel0_down _ hk))
  | fromReaction =>
    rintro ⟨x, ⟨⟩⟩ ⟨x', ⟨⟩⟩ ⟨hx, -⟩
    have hx : x.name = x'.name := hx.1
    show Sender.Rel R (.reaction x.name) (.reaction x'.name)
    rw [hx]
    exact .reaction _
  | external | scope | values | create | response | scenario | stepCommand | stepQuery | stepWait
  | stepAnswerCommand | stepAnswerQuery | stepEvent | stepCommandThen => intro _ _ _; trivial

/-! The fundamental lemma. -/

/-- Environments related by `R`. -/
abbrev Ty.relsV (R : PBij) (ts : List Ty) : Ty.dens ts → Ty.dens ts → Prop := Ty.relsWith Dsl.val (Dsl.relV R) R ts

section Access

theorem Var.get_rel : {Γ : List Ty} → {t : Ty} → (v : Var Γ t) → {ρ ρ' : Ty.dens Γ} → Ty.relsV R Γ ρ ρ' →
    Ty.relV R t (v.get ρ) (v.get ρ')
  | _ :: _, _, .here, _, _, h => h.1
  | _ :: _, _, .there v, _, _, h => Var.get_rel v h.2

theorem Dens.append_rel : {a b : List Ty} → {x x' : Ty.dens a} → {y y' : Ty.dens b} → Ty.relsV R a x x' →
    Ty.relsV R b y y' → Ty.relsV R (a ++ b) (Dens.append x y) (Dens.append x' y')
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, _, _, _, _, ⟨h1, h⟩, h' => ⟨h1, Dens.append_rel h h'⟩

theorem Dens.get_rel : {ts : List Ty} → {x y : Ty.dens ts} → Ty.relsV R ts x y → (k : Fin ts.length) →
    Ty.relV R (ts.get k) (Dens.get x k) (Dens.get y k)
  | _ :: _, _, _, h, ⟨0, _⟩ => h.1
  | _ :: _, _, _, h, ⟨k + 1, hk⟩ => Dens.get_rel h.2 ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem Dens.field_rel : {ts : List Ty} → {t : Ty} → {x y : Ty.dens ts} → Ty.relsV R ts x y → (k : Nat) →
    (h : ts[k]? = some t) → Ty.relV R t (Dens.field x k h) (Dens.field y k h)
  | [], _, _, _, _, _, h => nomatch h
  | t0 :: _, t, _, _, hxy, 0, h => by
    have e : t0 = t := by simpa using h
    subst e
    exact hxy.1
  | _ :: _, _, _, _, hxy, k + 1, h => Dens.field_rel hxy.2 k (by simpa using h)

theorem Alts.inj_rel : {vs : List (List Ty)} → (v : Fin vs.length) → {x y : Ty.dens (vs.get v)} →
    Ty.relsV R (vs.get v) x y → Ty.relAltsWith Dsl.val (Dsl.relV R) R vs (Alts.inj v x) (Alts.inj v y)
  | _ :: _, ⟨0, _⟩, _, _, h => h
  | _ :: _, ⟨k + 1, hk⟩, _, _, h => Alts.inj_rel (vs := _) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ h

theorem Alts.proj_rel : {vs : List (List Ty)} → {x y : Ty.alts vs} → Ty.relAltsWith Dsl.val (Dsl.relV R) R vs x y →
    (v : Fin vs.length) → Option.Rel (Ty.relsV R (vs.get v)) (Alts.proj x v) (Alts.proj y v)
  | [], x, _, _, _ => nomatch x
  | _ :: _, .inl _, .inl _, h, ⟨0, _⟩ => .some h
  | _ :: _, .inl _, .inl _, _, ⟨_ + 1, _⟩ => .none
  | _ :: _, .inr _, .inr _, _, ⟨0, _⟩ => .none
  | _ :: vs, .inr _, .inr _, h, ⟨k + 1, hk⟩ => Alts.proj_rel (vs := vs) h ⟨k, by simp at hk; omega⟩
  | _ :: _, .inl _, .inr _, h, _ | _ :: _, .inr _, .inl _, h, _ => h.elim

theorem Alts.only_rel {fs : List Ty} {x y : Ty.alts [fs]} (h : Ty.relAltsWith Dsl.val (Dsl.relV R) R [fs] x y) :
    Ty.relsV R fs (Alts.only x) (Alts.only y) := by
  match x, y, h with
  | .inl _, .inl _, h => exact h

theorem Alts.field_rel {ft : Ty} (k : Nat) : {vs : List (List Ty)} → (hk : ∀ fs ∈ vs, fs[k]? = some ft) →
    {x y : Ty.alts vs} → Ty.relAltsWith Dsl.val (Dsl.relV R) R vs x y →
    Ty.relV R ft (Dens.field (Alts.view x).2 k (hk _ (List.get_mem _ (Alts.view x).1)))
      (Dens.field (Alts.view y).2 k (hk _ (List.get_mem _ (Alts.view y).1)))
  | [], _, x, _, _ => nomatch x
  | _ :: _, _, .inl _, .inl _, h => Dens.field_rel h k _
  | _ :: _, hk, .inr _, .inr _, h =>
    Alts.field_rel k (fun fs hfs => hk fs (List.mem_cons_of_mem _ hfs)) h
  | _ :: _, _, .inl _, .inr _, h | _ :: _, _, .inr _, .inl _, h => h.elim

end Access

theorem optionRel_bind {α β γ δ : Type} {r : α → β → Prop} {s : γ → δ → Prop} {a : Option α} {b : Option β}
    {f : α → Option γ} {g : β → Option δ} (h : Option.Rel r a b) (hfg : ∀ x y, r x y → Option.Rel s (f x) (g y)) :
    Option.Rel s (a.bind f) (b.bind g) := by
  cases h with
  | none => exact .none
  | some hxy => exact hfg _ _ hxy

theorem optionRel_map {α β γ δ : Type} {r : α → β → Prop} {s : γ → δ → Prop} {a : Option α} {b : Option β}
    {f : α → γ} {g : β → δ} (h : Option.Rel r a b) (hfg : ∀ x y, r x y → s (f x) (g y)) :
    Option.Rel s (a.map f) (b.map g) := by
  cases h with
  | none => exact .none
  | some hxy => exact .some (hfg _ _ hxy)

mutual
theorem Pat.match_rel {t : Ty} {Δ : List Ty} : (p : Pat t Δ) → {x y : t.den} → Ty.relV R t x y →
    Option.Rel (Ty.relsV R Δ) (p.match x) (p.match y)
  | .wild, _, _, _ => .some trivial
  | .bind, _, _, h => .some ⟨h, trivial⟩
  | .int n, x, y, h => by
    have h : x = y := h
    subst h
    show Option.Rel _ (if _ then _ else _) (if _ then _ else _)
    split
    · exact .some trivial
    · exact .none
  | .str s, x, y, h => by
    have h : x = y := h
    subst h
    show Option.Rel _ (if _ then _ else _) (if _ then _ else _)
    split
    · exact .some trivial
    · exact .none
  | .tuple ps, _, _, h => Pats.match_rel ps h
  | .ctor v ps, x, y, h =>
    show Option.Rel _ ((Alts.proj x v).bind (Pats.match ps)) ((Alts.proj y v).bind (Pats.match ps)) from
    optionRel_bind (Alts.proj_rel h v) fun _ _ hxy => Pats.match_rel ps hxy
  | .as p, x, y, h =>
    show Option.Rel _ ((Pat.match p x).map _) ((Pat.match p y).map _) from
    optionRel_map (Pat.match_rel p h) fun _ _ hd => Dens.append_rel hd ⟨h, trivial⟩
theorem Pats.match_rel {ts : List Ty} {Δ : List Ty} : (ps : Pats ts Δ) → {x y : Ty.dens ts} → Ty.relsV R ts x y →
    Option.Rel (Ty.relsV R Δ) (ps.match x) (ps.match y)
  | .nil, _, _, _ => .some trivial
  | .cons p ps, _, _, ⟨h1, h⟩ =>
    optionRel_bind (Pat.match_rel p h1) fun _ _ ha => optionRel_map (Pats.match_rel ps h) fun _ _ hb => Dens.append_rel ha hb
end

theorem BinOp.eval_rel {a b c : Ty} (op : BinOp a b c) {x x' : a.den} {y y' : b.den} (hx : Ty.relV R a x x')
    (hy : Ty.relV R b y y') : Ty.relV R c (op.eval x y) (op.eval x' y') := by
  cases op with
  | add | sub | mul | div | mod | concat =>
    have hx : x = x' := hx
    have hy : y = y' := hy
    subst hx hy; rfl
  | lt | le | gt | ge =>
    have hx : x = x' := hx
    have hy : y = y' := hy
    subst hx hy; exact Ty.relV_ofBool _
  | and | or => exact Ty.relV_ofBool_eq (by rw [Ty.relV_bool hx, Ty.relV_bool hy])
  | eq h => exact Ty.relV_ofBool_eq (Ty.relV_deq h hx hy)
  | ne h => exact Ty.relV_ofBool_eq (by rw [Ty.relV_deq h hx hy])

section
variable {G : List Ty} (D : Defs G)

mutual
/-- Expressions evaluated in related environments give related values. -/
theorem Expr.eval_rel (hD : Ty.relsV R G D.eval D.eval) {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → {ρ ρ' : Ty.dens Γ} → Ty.relsV R Γ ρ ρ' →
    Ty.relV R t (e.eval D D.eval ρ) (e.eval D D.eval ρ')
  | .int _, _, _, _ => rfl
  | .str _, _, _, _ => rfl
  | .var v, _, _, h => Var.get_rel v h
  | .global v, _, _, _ => Var.get_rel v hD
  | .ctor v es, _, _, h => Alts.inj_rel v (Exprs.eval_rel hD es h)
  | .field _ k hk e, _, _, h => Alts.field_rel k hk (Expr.eval_rel hD e h)
  | .index e k, _, _, h => Dens.get_rel (Expr.eval_rel hD e h) k
  | .update e p, _, _, h =>
    Alts.inj_rel (vs := [_]) ⟨0, by simp⟩ (Patch.eval_rel hD p h (Alts.only_rel (Expr.eval_rel hD e h)))
  | .call f args, _, _, h => Expr.eval_rel hD f h _ _ (Exprs.eval_rel hD args h)
  | .lam body, _, _, h => fun _ _ hxs => Expr.eval_rel hD body (Dens.append_rel hxs h)
  | .let_ e body, _, _, h => Expr.eval_rel hD body ⟨Expr.eval_rel hD e h, h⟩
  | .case e cs hc, _, _, h => Clauses.eval_rel hD cs h (Expr.eval_rel hD e h) _ _
  | .list items, _, _, h => Items.eval_rel hD items h
  | .tuple es, _, _, h => Exprs.eval_rel hD es h
  | .bin op l r, _, _, h => BinOp.eval_rel op (Expr.eval_rel hD l h) (Expr.eval_rel hD r h)
  | .not e, _, _, h => Ty.relV_ofBool_eq (by rw [Ty.relV_bool (Expr.eval_rel hD e h)])
  | .neg e, _, _, h => by
    have he : Expr.eval D D.eval e _ = Expr.eval D D.eval e _ := Expr.eval_rel hD e h
    show @Neg.neg Int _ _ = @Neg.neg Int _ _
    rw [he]
  | .prim p args hp, _, _, _ => Prim.den_rel p args hp
  | .close _ env hΓ ht body, _, _, h => by
    show Ty.rel0 R _ (Fun.fn _) (Fun.fn _)
    refine Ty.rel0_down ht (Expr.eval_rel hD body ?_)
    erw [Ty.up_down, Ty.up_down]
    exact Exprs.eval_rel hD env h
  | .closeEffect _ env hΓ _ _, _, _, h => fun he => by
    obtain ⟨-, -, -, -, he, -⟩ := EffectFun.mk.inj he
    have hr := Ty.rel0_down hΓ (Exprs.eval_rel hD env h)
    rw [← eq_of_heq he] at hr
    exact hr
theorem Exprs.eval_rel (hD : Ty.relsV R G D.eval D.eval) {Γ : List Ty} {ts : List Ty} : (es : Exprs G Γ ts) → {ρ ρ' : Ty.dens Γ} →
    Ty.relsV R Γ ρ ρ' → Ty.relsV R ts (Exprs.eval D D.eval es ρ) (Exprs.eval D D.eval es ρ')
  | .nil, _, _, _ => trivial
  | .cons e es, _, _, h => ⟨Expr.eval_rel hD e h, Exprs.eval_rel hD es h⟩
theorem Items.eval_rel (hD : Ty.relsV R G D.eval D.eval) {Γ : List Ty} {t : Ty} : (items : Items G Γ t) → {ρ ρ' : Ty.dens Γ} →
    Ty.relsV R Γ ρ ρ' → Forall2 (Ty.relV R t) (Items.eval D D.eval items ρ) (Items.eval D D.eval items ρ')
  | .nil, _, _, _ => trivial
  | .cons e es, _, _, h => ⟨Expr.eval_rel hD e h, Items.eval_rel hD es h⟩
theorem Patch.eval_rel (hD : Ty.relsV R G D.eval D.eval) {Γ : List Ty} {ts : List Ty} : (p : Patch G Γ ts) → {ρ ρ' : Ty.dens Γ} →
    Ty.relsV R Γ ρ ρ' → {x x' : Ty.dens ts} → Ty.relsV R ts x x' →
    Ty.relsV R ts (Patch.eval D D.eval p ρ x) (Patch.eval D D.eval p ρ' x')
  | .nil, _, _, _, _, _, _ => trivial
  | .keep rest, _, _, h, _, _, ⟨h1, hx⟩ => ⟨h1, Patch.eval_rel hD rest h hx⟩
  | .set e rest, _, _, h, _, _, ⟨_, hx⟩ => ⟨Expr.eval_rel hD e h, Patch.eval_rel hD rest h hx⟩
theorem Clauses.eval_rel (hD : Ty.relsV R G D.eval D.eval) {Γ : List Ty} {t r : Ty} {sh : List Shape} : (cs : Clauses G Γ t r sh) →
    {ρ ρ' : Ty.dens Γ} → Ty.relsV R Γ ρ ρ' → {x y : t.den} → Ty.relV R t x y →
    (hx : ∃ s ∈ sh, Shape.Matches t s x) → (hy : ∃ s ∈ sh, Shape.Matches t s y) →
    Ty.relV R r (Clauses.eval D D.eval cs ρ x hx) (Clauses.eval D D.eval cs ρ' y hy)
  | .nil, _, _, _, _, _, _, hx, _ => False.elim (by simp at hx)
  | .cons p body rest, _, _, h, x, y, hxy, hx, hy => by
    have hm := Pat.match_rel p hxy
    unfold Clauses.eval
    split
    · next δ h1 =>
      split
      · next δ' h2 =>
        rw [h1, h2] at hm
        cases hm with
        | some hd => exact Expr.eval_rel hD body (Dens.append_rel hd h)
      · next h2 => rw [h1, h2] at hm; cases hm
    · next h1 =>
      split
      · next δ' h2 => rw [h1, h2] at hm; cases hm
      · next h2 => exact Clauses.eval_rel hD rest h hxy _ _
  | .guarded p guard body rest, _, _, h, x, y, hxy, hx, hy => by
    have hm := Pat.match_rel p hxy
    unfold Clauses.eval
    revert hm
    generalize p.match x = mx
    generalize p.match y = my
    intro hm
    cases hm with
    | none => exact Clauses.eval_rel hD rest h hxy _ _
    | some hd =>
      dsimp only
      rw [Ty.relV_bool (Expr.eval_rel hD guard (Dens.append_rel hd h))]
      split
      · exact Expr.eval_rel hD body (Dens.append_rel hd h)
      · exact Clauses.eval_rel hD rest h hxy _ _
end

end

/-- Every global relates to itself: each is an expression over the ones before it. -/
theorem Defs.eval_rel : {G : List Ty} → (D : Defs G) → Ty.relsV R G D.eval D.eval
  | [], .nil => trivial
  | _ :: _, .snoc defs _ body => ⟨Expr.eval_rel defs (Defs.eval_rel defs) body trivial, Defs.eval_rel defs⟩

/-- A kept function that returns effects maps related arguments to related effects when the values it captured relate
to themselves. -/
theorem EffectFun.apply_rel {ps : List Ty} {r : Ty} (f : EffectFun ps r) (h : Ty.rel0 R (.tuple f.Γ) f.env f.env)
    {xs ys : (Ty.tuple ps).den0} (hxy : Ty.rel0 R (.tuple ps) xs ys) : Ty.relV R r (f.apply xs) (f.apply ys) :=
  Expr.eval_rel f.defs (Defs.eval_rel f.defs) f.body ((Ty.relsV_up f.Γ f.hΓ f.env f.env).2 h) _ _
    ((Ty.relsV_up ps f.hps xs ys).2 hxy)

end Tazuna.Ir
