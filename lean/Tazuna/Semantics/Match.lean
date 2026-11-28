import Tazuna.Semantics.Value

/-! Pattern matching, and the proof that the exhaustiveness check is sound: when a case passes it, some unguarded
clause matches every value, so evaluation needs no failure. -/

namespace Tazuna.Ir

mutual
/-- The values a pattern binds, the first binding innermost, when it matches. -/
def Pat.match {t : Ty} {Δ : List Ty} : Pat t Δ → t.den → Option (Ty.dens Δ)
  | .wild, _ => some ()
  | .bind, x => some (x, ())
  | .int n, x => if @BEq.beq Int _ x n then some () else none
  | .str s, x => if @BEq.beq Str _ x s then some () else none
  | .tuple ps, x => Pats.match ps x
  | .ctor v ps, x => (Alts.proj x v).bind (Pats.match ps)
  | .as p, x => (Pat.match p x).map fun δ => Dens.append δ (x, ())
def Pats.match {ts : List Ty} {Δ : List Ty} : Pats ts Δ → Ty.dens ts → Option (Ty.dens Δ)
  | .nil, () => some ()
  | .cons p ps, (x, xs) => (Pat.match p x).bind fun a => (Pats.match ps xs).map fun b => Dens.append a b
end

namespace Shape

mutual
/-- The values a shape stands for. A literal stands for none, so the check never counts on one. -/
def Matches : (t : Ty) → Shape → t.den → Prop
  | _, .any, _ => True
  | _, .lit, _ => False
  | .tuple ts, .ctor k args, x => k = 0 ∧ MatchesAll ts args x
  | .adt _ _ vs, .ctor k args, x => MatchesAlt vs k args x
  | .int, .ctor .., _ | .str, .ctor .., _ | .list _, .ctor .., _ | .fn .., .ctor .., _ | .param _, .ctor .., _
  | .bag _, .ctor .., _ | .table .., .ctor .., _ | .point _, .ctor .., _ | .id, .ctor .., _
  | .dsl .., .ctor .., _ => False
def MatchesAll : (ts : List Ty) → List Shape → Ty.dens ts → Prop
  | [], [], _ => True
  | t :: ts, s :: ss, (x, xs) => Matches t s x ∧ MatchesAll ts ss xs
  | [], _ :: _, _ | _ :: _, [], _ => False
def MatchesAlt : (vs : List (List Ty)) → Nat → List Shape → Ty.alts vs → Prop
  | fs :: _, 0, args, .inl x => MatchesAll fs args x
  | _ :: vs, k + 1, args, .inr x => MatchesAlt vs k args x
  | _ :: _, 0, _, .inr _ | _ :: _, _ + 1, _, .inl _ => False
end

theorem matches_any : {t : Ty} → (x : t.den) → Matches t .any x
  | .int, _ | .str, _ | .list _, _ | .tuple _, _ | .fn .., _ | .adt .., _ | .param _, _
  | .bag _, _ | .table .., _ | .point _, _ | .id, _ | .dsl .., _ => trivial

theorem matchesAlt_inj : {vs : List (List Ty)} → (v : Fin vs.length) → (args : List Shape) →
    (y : Ty.dens (vs.get v)) → MatchesAll (vs.get v) args y → MatchesAlt vs v.val args (Alts.inj v y)
  | _ :: _, ⟨0, _⟩, _, _, h => h
  | _ :: _, ⟨k + 1, hk⟩, args, y, h => matchesAlt_inj (vs := _) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ args y h

theorem proj_of_matchesAlt : {vs : List (List Ty)} → (v : Fin vs.length) → (args : List Shape) →
    (x : Ty.alts vs) → MatchesAlt vs v.val args x → ∃ y, Alts.proj x v = some y ∧ MatchesAll (vs.get v) args y
  | _ :: _, ⟨0, _⟩, _, .inl y, h => ⟨y, rfl, h⟩
  | _ :: _, ⟨k + 1, hk⟩, args, .inr x, h => proj_of_matchesAlt (vs := _) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ args x h
  | _ :: _, ⟨0, _⟩, _, .inr _, h => nomatch h
  | _ :: _, ⟨_ + 1, _⟩, _, .inl _, h => nomatch h

end Shape

mutual
/-- A pattern matches every value its shape stands for. -/
theorem Pat.match_of_matches {t : Ty} {Δ : List Ty} :
    (p : Pat t Δ) → (x : t.den) → Shape.Matches t p.shape x → (p.match x).isSome
  | .wild, _, _ => rfl
  | .bind, _, _ => rfl
  | .int _, _, h => nomatch h
  | .str _, _, h => nomatch h
  | .tuple ps, x, h => by
    simp only [Pat.shape, Shape.Matches] at h
    simp only [Pat.match]
    exact Pats.match_of_matches ps x h.2
  | .ctor v ps, x, h => by
    simp only [Pat.shape, Shape.Matches] at h
    obtain ⟨y, hy, hm⟩ := Shape.proj_of_matchesAlt v _ x h
    simp only [Pat.match, hy, Option.bind_some]
    exact Pats.match_of_matches ps y hm
  | .as p, x, h => by
    simp only [Pat.shape] at h
    have := Pat.match_of_matches p x h
    simp only [Pat.match, Option.isSome_map]
    exact this
theorem Pats.match_of_matches {ts : List Ty} {Δ : List Ty} :
    (ps : Pats ts Δ) → (xs : Ty.dens ts) → Shape.MatchesAll ts ps.shapes xs → (ps.match xs).isSome
  | .nil, (), _ => rfl
  | .cons p ps, (x, xs), h => by
    simp only [Pats.shapes, Shape.MatchesAll] at h
    have h1 := Pat.match_of_matches p x h.1
    have h2 := Pats.match_of_matches ps xs h.2
    simp only [Pats.match]
    cases e1 : p.match x with
    | none => simp [e1] at h1
    | some a =>
      cases e2 : ps.match xs with
      | none => simp [e2] at h2
      | some b => simp
end

namespace Shape

theorem matchesAll_append : {fs ts : List Ty} → (A B : List Shape) → (y : Ty.dens fs) → (xs : Ty.dens ts) →
    A.length = fs.length → MatchesAll (fs ++ ts) (A ++ B) (Dens.append y xs) →
    MatchesAll fs A y ∧ MatchesAll ts B xs
  | [], _, [], _, (), _, _, h => ⟨trivial, h⟩
  | _ :: _, _, a :: A, B, (y, ys), xs, hl, h => by
    simp only [List.cons_append, Dens.append, MatchesAll] at h ⊢
    have := matchesAll_append A B ys xs (by simpa using hl) h.2
    exact ⟨⟨h.1, this.1⟩, this.2⟩
  | [], _, _ :: _, _, _, _, hl, _ => nomatch hl
  | _ :: _, _, [], _, _, _, hl, _ => nomatch hl

/-- A row of the matrix specialized by variant `k` comes from a row of the original matrix, which matches the whole
value when the specialized row matches its fields. -/
theorem specialize_sound {t : Ty} {fs ts : List Ty} (k : Nat) (x : t.den) (y : Ty.dens fs) (xs : Ty.dens ts)
    (hx : ∀ args, args.length = fs.length → MatchesAll fs args y → Matches t (.ctor k args) x) :
    (rows : List (List Shape)) → (row' : List Shape) → row' ∈ specialize k fs.length rows →
    MatchesAll (fs ++ ts) row' (Dens.append y xs) → ∃ row ∈ rows, MatchesAll (t :: ts) row (x, xs)
  | [], _, hm, _ => nomatch hm
  | (.any :: rest) :: rows, row', hm, h => by
    simp only [specialize, List.mem_cons] at hm
    rcases hm with rfl | hm
    · have := matchesAll_append _ rest y xs (by simp) h
      exact ⟨.any :: rest, by simp, matches_any x, this.2⟩
    · obtain ⟨row, hr, hmr⟩ := specialize_sound k x y xs hx rows row' hm h
      exact ⟨row, by simp [hr], hmr⟩
  | (.ctor j args :: rest) :: rows, row', hm, h => by
    simp only [specialize] at hm
    split at hm
    · rename_i hj
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · have := matchesAll_append args rest y xs hj.2 h
        refine ⟨.ctor j args :: rest, by simp, ?_, this.2⟩
        rw [hj.1]
        exact hx args hj.2 this.1
      · obtain ⟨row, hr, hmr⟩ := specialize_sound k x y xs hx rows row' hm h
        exact ⟨row, by simp [hr], hmr⟩
    · obtain ⟨row, hr, hmr⟩ := specialize_sound k x y xs hx rows row' hm h
      exact ⟨row, by simp [hr], hmr⟩
  | [] :: rows, row', hm, h | (.lit :: _) :: rows, row', hm, h => by
    simp only [specialize] at hm
    obtain ⟨row, hr, hmr⟩ := specialize_sound k x y xs hx rows row' hm h
    exact ⟨row, by simp [hr], hmr⟩

theorem dflt_sound {t : Ty} {ts : List Ty} (x : t.den) (xs : Ty.dens ts) :
    (rows : List (List Shape)) → (row' : List Shape) → row' ∈ dflt rows → MatchesAll ts row' xs →
    ∃ row ∈ rows, MatchesAll (t :: ts) row (x, xs)
  | [], _, hm, _ => nomatch hm
  | (.any :: rest) :: rows, row', hm, h => by
    simp only [dflt, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨.any :: row', by simp, matches_any x, h⟩
    · obtain ⟨row, hr, hmr⟩ := dflt_sound x xs rows row' hm h
      exact ⟨row, by simp [hr], hmr⟩
  | [] :: rows, row', hm, h | (.lit :: _) :: rows, row', hm, h | (.ctor .. :: _) :: rows, row', hm, h => by
    simp only [dflt] at hm
    obtain ⟨row, hr, hmr⟩ := dflt_sound x xs rows row' hm h
    exact ⟨row, by simp [hr], hmr⟩

theorem eachVariant_get (c : List (List Shape) → List Ty → Bool) (rows : List (List Shape)) (ts : List Ty) :
    (k : Nat) → (vs : List (List Ty)) → eachVariant c rows ts k vs = true → (v : Fin vs.length) →
    c (specialize (k + v.val) (vs.get v).length rows) (vs.get v ++ ts) = true
  | _, [], _, v => v.elim0
  | k, _ :: _, h, ⟨0, _⟩ => by
    simp only [eachVariant, Bool.and_eq_true] at h
    simpa using h.1
  | k, _ :: vs, h, ⟨j + 1, hj⟩ => by
    simp only [eachVariant, Bool.and_eq_true] at h
    have := eachVariant_get c rows ts (k + 1) vs h.2 ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    simp only [List.get_cons_succ]
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact this

/-- What `covers` decides: every list of values matches some row. -/
theorem covers_sound : (fuel : Nat) → (rows : List (List Shape)) → (ts : List Ty) → covers fuel rows ts = true →
    (xs : Ty.dens ts) → ∃ row ∈ rows, MatchesAll ts row xs
  | _, rows, [], h, () => by
    simp only [covers, List.any_eq_true] at h
    obtain ⟨row, hr, he⟩ := h
    cases row with
    | nil => exact ⟨[], hr, trivial⟩
    | cons => simp at he
  | 0, _, _ :: _, h, _ => by simp [covers] at h
  | n + 1, rows, .adt i args vs :: ts, h, (x, xs) => by
    simp only [covers] at h
    have hv := eachVariant_get (covers n) rows ts 0 vs h (Alts.view x).1
    rw [Nat.zero_add] at hv
    obtain ⟨row', hr', hm'⟩ := covers_sound n _ _ hv (Dens.append (Alts.view x).2 xs)
    refine specialize_sound (t := .adt i args vs) _ x (Alts.view x).2 xs ?_ rows row' hr' hm'
    intro as _ hm
    have := matchesAlt_inj (Alts.view x).1 as _ hm
    have e : Alts.inj (Alts.view x).1 (Alts.view x).2 = x := Alts.inj_view (vs := vs) x
    simp only [Matches]
    rw [e] at this
    exact this
  | n + 1, rows, .tuple us :: ts, h, (x, xs) => by
    simp only [covers] at h
    obtain ⟨row', hr', hm'⟩ := covers_sound n _ _ h (Dens.append (a := us) (b := ts) x xs)
    exact specialize_sound (t := .tuple us) 0 x x xs (fun as _ hm => ⟨rfl, hm⟩) rows row' hr' hm'
  | n + 1, rows, .int :: ts, h, (x, xs) | n + 1, rows, .str :: ts, h, (x, xs)
  | n + 1, rows, .list _ :: ts, h, (x, xs) | n + 1, rows, .fn .. :: ts, h, (x, xs)
  | n + 1, rows, .param _ :: ts, h, (x, xs) | n + 1, rows, .bag _ :: ts, h, (x, xs)
  | n + 1, rows, .table .. :: ts, h, (x, xs) | n + 1, rows, .point _ :: ts, h, (x, xs)
  | n + 1, rows, .id :: ts, h, (x, xs) | n + 1, rows, .dsl .. :: ts, h, (x, xs) => by
    simp only [covers] at h
    obtain ⟨row', hr', hm'⟩ := covers_sound n _ _ h xs
    exact dflt_sound x xs rows row' hr' hm'

end Shape

/-- An exhaustive case has an unguarded clause for every value. -/
theorem Exhaustive.sound {t : Ty} {sh : List Shape} (h : Exhaustive t sh) (x : t.den) :
    ∃ s ∈ sh, Shape.Matches t s x := by
  obtain ⟨fuel, hc⟩ := h
  obtain ⟨row, hr, hm⟩ := Shape.covers_sound fuel _ [t] hc (x, ())
  simp only [List.mem_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  exact ⟨s, hs, hm.1⟩

end Tazuna.Ir
