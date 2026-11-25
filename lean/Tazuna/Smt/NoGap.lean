import Tazuna.Smt.CheckedState

/-! No layout gap: the expression encoder, run in a layout that covers the program (`Covers`), refuses only for a
reason that is the spec's (a limit, a string outside SMT-LIB's, a case the types rule out), never because the layout
lacks a datatype or a kind of effect. The proof is a logical relation over codes (`CodeOk`), as T1's: a term code's
type has its datatypes in the layout whenever it has a sort (`Avail`), a function code maps related arguments to a
result with no gap, and a handle's or a kept function's code names what the program declares and writes. Every
lookup the encoder makes is at a type some code or node of the program has, so it succeeds, or the type has no sort
and the refusal is the limit `unsortable`. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Whether a refusal is a gap of the layout, the builder's fault. -/
def Refusal.gap : Refusal → Bool
  | .layout _ => true
  | _ => false

/-- The result is no layout gap, and a value satisfies `p`. -/
def Sound {α : Type} (p : α → Prop) : Except Refusal α → Prop
  | .ok a => p a
  | .error r => r.gap = false

section
variable {α β : Type} {p : α → Prop} {q : β → Prop}

theorem sound_bind {x : Except Refusal α} {f : α → Except Refusal β} (hx : Sound p x) (hf : ∀ a, p a → Sound q (f a)) :
    Sound q (x >>= f) := by
  cases x with
  | error r => exact hx
  | ok a => exact hf a hx

theorem sound_bind_ok {x : Except Refusal α} {f : α → Except Refusal β} {a : α} (hx : x = .ok a) (hf : Sound q (f a)) :
    Sound q (x >>= f) := by
  subst hx; exact hf

theorem sound_mono {x : Except Refusal α} {p' : α → Prop} (hx : Sound p x) (h : ∀ a, p a → p' a) : Sound p' x := by
  cases x with
  | error r => exact hx
  | ok a => exact h a hx

theorem sound_need {r : Refusal} {o : Option α} (h : o = none → r.gap = false) : Sound (fun a => o = some a) (need r o) := by
  cases o with
  | none => exact h rfl
  | some a => rfl

theorem sound_need' {r : Refusal} (hr : r.gap = false) (b : Bool) (a : α) : Sound (fun x => x = a) (need' r b a) := by
  unfold need'; split
  · rfl
  · exact hr

end

theorem gap_limit (l : Limit) : (Refusal.limit l).gap = false := rfl
theorem gap_unexpected (u : Unexpected) : (Refusal.unexpected u).gap = false := rfl
theorem gap_string (s : String) : (Refusal.unencodableString s).gap = false := rfl

section
variable (L : Layout)

/-- The type's datatypes are in the layout whenever it has a sort. -/
def Avail (t : Ty) : Prop := t.sorted = true → L.Has t

/-- Every datatype of the layout has a sort, so a type it finds has one, and every kind of effect's fields are data
with sorts. -/
structure SortedLayout : Prop where
  types : ∀ p ∈ L.types, p.1.sorted = true
  effects : ∀ k ∈ L.effects, Ty.sorteds k.fields = true ∧ (Ty.tuple k.fields).isData = true
  owns : ∀ k ∈ L.owns, Ty.sorteds k.fields = true ∧ (Ty.tuple k.fields).isData = true

end

section
variable {L : Layout}

theorem sorted_of_find (hL : SortedLayout L) {t : Ty} {x : Nat × Nat} (h : L.find? t = some x) : t.sorted = true := by
  simp only [Layout.find?, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨u, m⟩, j⟩, hfind, -⟩ := h
  have hs := List.find?_some hfind
  have hu := eq_of_same (by simpa using hs)
  subst hu
  exact hL.types _ (List.fst_mem_of_mem_zipIdx (List.mem_of_find?_eq_some hfind))

theorem lacks_gap {t : Ty} (h : (lacks t).gap = true) : t.sorted = true := by
  unfold lacks at h; split at h
  · assumption
  · cases h

/-- A lookup whose type is available succeeds or is refused as the type having no sort. -/
theorem sound_lacks {α : Type} {t : Ty} {o : Option α} (ha : Avail L t) (hf : L.Has t → o.isSome = true) :
    Sound (fun a => o = some a) (need (lacks t) o) :=
  sound_need fun ho => by
    cases hg : (lacks t).gap with
    | false => rfl
    | true => have := hf (ha (lacks_gap hg)); simp [ho] at this

theorem has_of_find (hL : SortedLayout L) {t : Ty} (ha : Avail L t) {x : Nat × Nat} (h : L.find? t = some x) : L.Has t :=
  ha (sorted_of_find hL h)

end

section
variable (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)

/-- The program writes a kept function of type `t` at the code's site, capturing values of the code's types. -/
def ClosOk (t : Ty) (c : ClosureCode) : Prop := ∃ s ∈ sitesOf P t, s.2.site = c.key.site ∧ s.1 = c.key.Γ

/-- Some external lists the handle in `ds`: its kind, a literal name and its types, as check compares them. -/
def Declares (h : HandleSite) : Prop :=
  ∃ n, h.name = some n ∧
    ds.any (fun xd => xd.2.kind == h.kind && xd.2.name == n && (Ty.sames xd.2.types h.types).isSome) = true

/-- What a structure value's code must say: a kept function's names a site of its type, a handle's what an external
declares or a handle the program makes, any other's is a term whose type is available. -/
def DslOk : (k : Dsl) → (a : List Ty) → DslCode k a → Prop
  | .closure, [t], c => ClosOk P t c
  | .closure, _, _ => True
  | .externalCommand, a, n => Declares ds ⟨"external command", some n, a⟩
  | .externalQuery, [i, o], (n, c) => Declares ds ⟨"external query", some n, [i, o]⟩ ∧ ClosOk P (.fn [i, o] Ty.rules) c
  | .externalQuery, _, _ => True
  | .command, a, n => ⟨"command", some n, a⟩ ∈ H
  | .query, a, n => ⟨"query", some n, a⟩ ∈ H
  | .spec, a, _ => Avail L (.dsl .spec a)
  | .service, a, _ => Avail L (.dsl .service a)
  | .machine, a, _ => Avail L (.dsl .machine a)
  | .reaction, a, _ => Avail L (.dsl .reaction a)
  | .external, a, _ => Avail L (.dsl .external a)
  | .source, a, _ => Avail L (.dsl .source a)
  | .declared, a, _ => Avail L (.dsl .declared a)
  | .effect, a, _ => Avail L (.dsl .effect a)
  | .subscription, a, _ => Avail L (.dsl .subscription a)
  | .bounds, a, _ => Avail L (.dsl .bounds a)
  | .create, a, _ => Avail L (.dsl .create a)
  | .response, a, _ => Avail L (.dsl .response a)
  | .scenario, a, _ => Avail L (.dsl .scenario a)
  | .step, a, _ => Avail L (.dsl .step a)
  | .sender, a, _ => Avail L (.dsl .sender a)
  | .fresh, a, _ => Avail L (.dsl .fresh a)
  | .effectClosure, a, _ => Avail L (.dsl .effectClosure a)

mutual
/-- A code with no gap behind it: a term's type is available, a function maps related arguments to a result with no
gap where the result's type is available, a structure value's code says what `DslOk` asks. -/
def CodeOk : (t : Ty) → Code t → Prop
  | .fn ps r, f => ∀ xs, CodesOk ps xs → Avail L r → Sound (fun p => CodeOk r p.1) (f xs)
  | .dsl k a, c => DslOk L P ds H k a c
  | .int, _ => Avail L .int
  | .str, _ => Avail L .str
  | .date, _ => Avail L .date
  | .id, _ => Avail L .id
  | .param i, _ => Avail L (.param i)
  | .list t, _ => Avail L (.list t)
  | .bag t, _ => Avail L (.bag t)
  | .tuple ts, _ => Avail L (.tuple ts)
  | .adt i a vs, _ => Avail L (.adt i a vs)
  | .table k v, _ => Avail L (.table k v)
def CodesOk : (ts : List Ty) → Codes ts → Prop
  | [], () => True
  | t :: ts, (c, cs) => CodeOk t c ∧ CodesOk ts cs
end

/-- Each global's code has no gap behind it. -/
def EncsOk : (G : List Ty) → Encs G → Prop
  | [], () => True
  | t :: G, (e, es) => Sound (fun p => CodeOk L P ds H t p.1) e ∧ EncsOk G es

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem codeOk_ofTerm : {t : Ty} → {x : Term} → {c : Code t} → Code.ofTerm? t x = some c → Avail L t →
    CodeOk L P ds H t c
  | .fn .., _, _, h, _ => by simp [Code.ofTerm?] at h
  | .dsl k a, _, _, h, ha => by cases k <;> simp_all [Code.ofTerm?, DslCode.ofTerm?, CodeOk, DslOk]
  | .int, _, _, _, ha | .str, _, _, _, ha | .date, _, _, _, ha | .id, _, _, _, ha | .param _, _, _, _, ha
  | .list _, _, _, _, ha | .bag _, _, _, _, ha | .tuple _, _, _, _, ha | .adt .., _, _, _, ha | .table .., _, _, _, ha => ha

theorem avail_of_term : {t : Ty} → {c : Code t} → {x : Term} → Code.term? t c = some x → CodeOk L P ds H t c →
    Avail L t
  | .fn .., _, _, h, _ => by simp [Code.term?] at h
  | .dsl k a, _, _, h, ha => by cases k <;> simp_all [Code.term?, DslCode.term?, CodeOk, DslOk]
  | .int, _, _, _, ha | .str, _, _, _, ha | .date, _, _, _, ha | .id, _, _, _, ha | .param _, _, _, _, ha
  | .list _, _, _, _, ha | .bag _, _, _, _, ha | .tuple _, _, _, _, ha | .adt .., _, _, _, ha | .table .., _, _, _, ha => ha

theorem codesOk_ofTerms : {ts : List Ty} → {xs : List Term} → {cs : Codes ts} → Codes.ofTerms? ts xs = some cs →
    (∀ t ∈ ts, Avail L t) → CodesOk L P ds H ts cs
  | [], [], (), _, _ => trivial
  | t :: ts, x :: xs, (c, cs), h, ha => by
    simp only [Codes.ofTerms?, Option.bind_eq_bind, Option.pure_def] at h
    cases hc : Code.ofTerm? t x with
    | none => simp [hc] at h
    | some c' =>
      cases hcs : Codes.ofTerms? ts xs with
      | none => simp [hc, hcs] at h
      | some cs' =>
        simp only [hc, hcs, Option.bind_some] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨codeOk_ofTerm hc (ha t (by simp)), codesOk_ofTerms hcs fun u hu => ha u (by simp [hu])⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [Codes.ofTerms?] at h

theorem codeOk_share : (t : Ty) → (c : Code t) → CodeOk L P ds H t c → CodeOk L P ds H t (Code.share t c)
  | .fn .., _, h => h
  | .dsl k a, _, h => by cases k <;> exact h
  | .int, _, h | .str, _, h | .date, _, h | .id, _, h | .param _, _, h
  | .list _, _, h | .bag _, _, h | .tuple _, _, h | .adt .., _, h | .table .., _, h => h

theorem codesOk_share : (ts : List Ty) → (cs : Codes ts) → CodesOk L P ds H ts cs →
    CodesOk L P ds H ts (Codes.share ts cs)
  | [], (), _ => trivial
  | t :: ts, (c, cs), ⟨h, hs⟩ => ⟨codeOk_share t c h, codesOk_share ts cs hs⟩

theorem codesOk_append : {a b : List Ty} → (xs : Codes a) → (ys : Codes b) → CodesOk L P ds H a xs →
    CodesOk L P ds H b ys → CodesOk L P ds H (a ++ b) (Codes.append xs ys)
  | [], _, (), _, _, h => h
  | _ :: _, _, (_, xs), ys, ⟨h, hs⟩, h' => ⟨h, codesOk_append xs ys hs h'⟩

theorem codeOk_var : {Γ : List Ty} → {t : Ty} → (v : Var Γ t) → (σ : Codes Γ) → CodesOk L P ds H Γ σ →
    CodeOk L P ds H t (v.code σ)
  | _ :: _, _, .here, (_, _), ⟨h, _⟩ => h
  | _ :: _, _, .there v, (_, ss), ⟨_, h⟩ => codeOk_var v ss h

theorem encOk_var : {G : List Ty} → {t : Ty} → (v : Var G t) → (gs : Encs G) → EncsOk L P ds H G gs →
    Sound (fun p => CodeOk L P ds H t p.1) (v.enc gs)
  | _ :: _, _, .here, (_, _), ⟨h, _⟩ => h
  | _ :: _, _, .there v, (_, ss), ⟨_, h⟩ => encOk_var v ss h

theorem avail_int : Avail L .int := fun _ => trivial
theorem avail_str : Avail L .str := fun _ => trivial

end

/-- `dsl` gives a default term for each structure type with a sort that `D` holds (only data when `fx` is false). -/
def DslDefaults (D : Dsl → List Ty → Prop) (dsl : Dsl → List Ty → Option Term) (fx : Bool) : Prop :=
  ∀ k a, (Ty.dsl k a).sorted = true → (fx = false → (Ty.dsl k a).isData = true) → D k a → (dsl k a).isSome = true

section
variable {L : Layout} {D : Dsl → List Ty → Prop} {dsl : Dsl → List Ty → Option Term} {fx : Bool}

mutual
/-- A type with a sort whose datatypes are in the layout has a default term, given one for each structure type it
holds (`fx` false: only data, so no effect). -/
theorem defaultWith_isSome (hd : DslDefaults D dsl fx) : (t : Ty) → Layout.HasWith L D t → t.sorted = true → (fx = false → t.isData = true) →
    (defaultWith L dsl t).isSome = true
  | .int, _, _, _ | .date, _, _, _ | .str, _, _, _ => rfl
  | .adt 0 _ vs, _, hs, _ => by simp only [Ty.sorted] at hs; simp [defaultWith, hs]
  | .adt (i + 1) a vs, ⟨hv, hf⟩, hs, hx => by
    obtain ⟨⟨d, n⟩, hd'⟩ := Option.isSome_iff_exists.1 hf
    have h := firstWith_isSome hd vs hv hs (by simpa [Ty.isData] using hx)
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 h
    simp [defaultWith, hd', hxs]
  | .tuple ts, ⟨hv, hf⟩, hs, hx => by
    obtain ⟨⟨d, n⟩, hd'⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 (defaultsWith_isSome hd ts hv hs (by simpa [Ty.isData] using hx))
    simp [defaultWith, hd', hxs]
  | .id, hf, _, _ => by
    obtain ⟨⟨d, n⟩, hd'⟩ := Option.isSome_iff_exists.1 hf
    simp [defaultWith, hd']
  | .bag t, ⟨hv, ht, hf⟩, hs, hx => by
    obtain ⟨⟨d, n⟩, hd'⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 ht
    obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 (defaultWith_isSome hd t hv hs (by simpa [Ty.isData] using hx))
    simp [defaultWith, hd', hdt, hx']
  | .list t, ⟨hv, ht, hf⟩, hs, hx => by
    obtain ⟨⟨d, n⟩, hd'⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 ht
    obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 (defaultWith_isSome hd t hv hs (by simpa [Ty.isData] using hx))
    simp [defaultWith, hd', hdt, hx']
  | .table k w, ⟨hk, hw, ht, hf⟩, hs, hx => by
    simp only [Ty.sorted, Bool.and_eq_true] at hs
    have hx2 : fx = false → k.isData = true ∧ w.isData = true := fun h => by simpa [Ty.isData] using hx h
    obtain ⟨⟨d, n⟩, hd'⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 ht
    obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 (defaultWith_isSome hd k hk hs.1 fun h => (hx2 h).1)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (defaultWith_isSome hd w hw hs.2 fun h => (hx2 h).2)
    simp [defaultWith, hd', hdt, hx', hy]
  | .dsl k a, hD, hs, hx => hd k a hs hx hD
  | .fn .., _, hs, _ | .param _, _, hs, _ => by simp [Ty.sorted] at hs
theorem defaultsWith_isSome (hd : DslDefaults D dsl fx) : (ts : List Ty) → Layout.HasWiths L D ts → Ty.sorteds ts = true →
    (fx = false → Ty.isDatas ts = true) → (defaultsWith L dsl ts).isSome = true
  | [], _, _, _ => rfl
  | t :: ts, ⟨ht, hts⟩, hs, hx => by
    simp only [Ty.sorteds, Bool.and_eq_true] at hs
    have hx2 : fx = false → t.isData = true ∧ Ty.isDatas ts = true := fun h => by simpa [Ty.isDatas] using hx h
    obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 (defaultWith_isSome hd t ht hs.1 fun h => (hx2 h).1)
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 (defaultsWith_isSome hd ts hts hs.2 fun h => (hx2 h).2)
    simp [defaultsWith, hx', hxs]
theorem firstWith_isSome (hd : DslDefaults D dsl fx) : (vs : List (List Ty)) → Layout.HasWithss L D vs → Ty.sortedss vs = true →
    (fx = false → Ty.isDatass vs = true) → (firstWith L dsl vs).isSome = true
  | [], _, _, _ => rfl
  | fs :: _, ⟨hfs, _⟩, hs, hx => by
    simp only [Ty.sortedss, Bool.and_eq_true] at hs
    exact defaultsWith_isSome hd fs hfs hs.1 fun h => by simp only [Ty.isDatass, Bool.and_eq_true] at hx; exact (hx h).1
end

end

section
variable {L : Layout}

theorem effectFields_sorted (hL : SortedLayout L) {e : Ty} {fs : List Ty} (h : fs ∈ L.effectFields e) :
    Ty.sorteds fs = true ∧ (Ty.tuple fs).isData = true := by
  simp only [Layout.effectFields, Layout.effectsOf, Layout.ownsOf, List.mem_append, List.mem_map, List.mem_filter] at h
  rcases h with ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
  · exact hL.effects k hk
  · exact hL.owns k hk

theorem sorted_dsl_data {k : Dsl} {a : List Ty} (h : (Ty.dsl k a).isData = true) : k = .fresh := by
  simpa [Ty.isData] using h

theorem hasWiths_of_head? {D : Dsl → List Ty → Prop} : {vs : List (List Ty)} → {fs : List Ty} →
    Layout.HasWithss L D vs → vs.head? = some fs → Layout.HasWiths L D fs
  | _ :: _, _, ⟨h, _⟩, rfl => h

theorem mapM_defaultWith (dsl : Dsl → List Ty → Option Term) : (fs : List Ty) →
    fs.mapM (defaultWith L dsl) = defaultsWith L dsl fs
  | [] => rfl
  | f :: fs => by
    simp only [List.mapM_cons, defaultsWith, mapM_defaultWith dsl fs]

/-- A type with a sort whose datatypes are in the layout has the default term free slots hold. -/
theorem defaultT_isSome (hL : SortedLayout L) {t : Ty} (h : L.Has t) (hs : t.sorted = true) : (defaultT L t).isSome = true := by
  refine defaultWith_isSome (fx := true) ?_ t h hs (by simp)
  intro k a hks _ hD
  match k, a, hks, hD with
  | .effect, [e], _, ⟨hfs, hf⟩ =>
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [effectDefault, hd]
    cases hh : (L.effectFields e).head? with
    | none => rfl
    | some fs =>
      obtain ⟨hso, hda⟩ := effectFields_sorted hL (List.mem_of_mem_head? hh)
      have hd' := defaultsWith_isSome (D := fun _ _ => True) (fx := false)
        (dsl := freshDefault) (fun k a _ hx _ => by
          obtain rfl := sorted_dsl_data (hx rfl); rfl) fs (hasWiths_of_head? hfs hh) hso
          (fun _ => by simpa [Ty.isData] using hda)
      rw [← mapM_defaultWith] at hd'
      obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.1 hd'
      simp [hys]
  | .fresh, _, _, _ => rfl
  | .effect, [], hks, _ | .effect, _ :: _ :: _, hks, _ => simp [Ty.sorted] at hks
  | .spec, _, hks, _ | .service, _, hks, _ | .command, _, hks, _ | .query, _, hks, _ | .machine, _, hks, _
  | .reaction, _, hks, _ | .external, _, hks, _ | .externalCommand, _, hks, _ | .externalQuery, _, hks, _
  | .source, _, hks, _ | .declared, _, hks, _ | .subscription, _, hks, _ | .bounds, _, hks, _ | .create, _, hks, _
  | .response, _, hks, _ | .scenario, _, hks, _ | .step, _, hks, _ | .sender, _, hks, _ | .closure, _, hks, _
  | .effectClosure, _, hks, _ => simp [Ty.sorted] at hks

end

section
variable {L : Layout}

/-- The layout found the type: its datatypes are in it, and it has a sort. -/
def Got (L : Layout) (t : Ty) : Prop := L.Has t ∧ t.sorted = true

theorem got_of_find (hL : SortedLayout L) {t : Ty} (ha : Avail L t) {x : Nat × Nat} (h : L.find? t = some x) : Got L t :=
  ⟨has_of_find hL ha h, sorted_of_find hL h⟩

theorem avail_of_got {t : Ty} (h : Got L t) : Avail L t := fun _ => h.1

theorem findE_sound (hL : SortedLayout L) {t : Ty} (ha : Avail L t) (hf : L.Has t → (L.find? t).isSome = true) :
    Sound (fun x => L.find? t = some x ∧ Got L t) (L.findE t) :=
  sound_mono (sound_lacks ha hf) fun _ hx => ⟨hx, got_of_find hL ha hx⟩

theorem tupleD_sound (hL : SortedLayout L) {ts : List Ty} (ha : Avail L (.tuple ts)) :
    Sound (fun d => (∃ n, L.find? (.tuple ts) = some (d, n)) ∧ Got L (.tuple ts)) (tupleD L ts) := by
  unfold tupleD; split
  · rename_i d n h; exact ⟨⟨n, h⟩, got_of_find hL ha h⟩
  · rename_i h
    cases hg : (lacks (.tuple ts)).gap with
    | false => exact hg
    | true => have := (ha (lacks_gap hg)).2; simp [h] at this

theorem adtCtor_sound {i : Nat} {a : List Ty} {vs : List (List Ty)} (ha : Avail L (.adt i a vs)) (k : Nat)
    (fs : List Term) : Sound (fun _ => True) (adtCtor L i a vs k fs) := by
  unfold adtCtor; split
  · split
    · trivial
    · rfl
  · split
    · trivial
    · rename_i i' _ h
      cases hg : (lacks (.adt (i' + 1) a vs)).gap with
      | false => exact hg
      | true => have := (ha (lacks_gap hg)).2; simp [h] at this

theorem adtView_sound (hL : SortedLayout L) {i : Nat} {a : List Ty} {vs : List (List Ty)} (ha : Avail L (.adt i a vs))
    (k : Fin vs.length) (x : Term) : Sound (fun _ => Got L (.adt i a vs)) (adtView L i a vs k x) := by
  unfold adtView; split
  · split
    · rename_i h; exact ⟨.inl (by simp [h]), by simp [Ty.sorted, h]⟩
    · rfl
  · split
    · rename_i h; exact got_of_find hL ha h
    · rename_i i' _ h
      cases hg : (lacks (.adt (i' + 1) a vs)).gap with
      | false => exact hg
      | true => have := (ha (lacks_gap hg)).2; simp [h] at this

theorem collD_sound (hL : SortedLayout L) {c : Ty} {item : List Ty} (ha : Avail L c)
    (hf : L.Has c → (L.find? c).isSome = true ∧ (L.find? (.tuple (Ty.bool :: item))).isSome = true) :
    Sound (fun r => L.find? c = some (r.1, r.2.1) ∧ Got L c) (collD L c item) := by
  unfold collD; split
  · rename_i d n dt _ h _; exact ⟨h, got_of_find hL ha h⟩
  · rename_i h
    cases hg : (lacks c).gap with
    | false => exact hg
    | true =>
      obtain ⟨h1, h2⟩ := hf (ha (lacks_gap hg))
      obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 h1
      obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 h2
      exact absurd (h d n dt m hd hdt) (by simp)

theorem defaultE_ok (hL : SortedLayout L) {t : Ty} (h : Got L t) : ∃ x, defaultE L t = .ok x := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (defaultT_isSome hL h.1 h.2)
  exact ⟨x, need_ok.2 hx⟩

theorem defaultItems_ok (hL : SortedLayout L) {item : List Ty} (h : ∀ t ∈ item, Got L t) :
    ∃ x, defaultItems L item = .ok x := by
  unfold defaultItems; split
  · exact ⟨_, rfl⟩
  · rename_i hn
    have := mapM_isSome (defaultT L) item
    simp only [hn, Option.isSome_none] at this
    exact absurd this.symm (by simpa [← Option.isSome_iff_ne_none] using fun t ht => defaultT_isSome hL (h t ht).1 (h t ht).2)

theorem emptySlots_ok (hL : SortedLayout L) {item : List Ty} (h : ∀ t ∈ item, Got L t) (n : Nat) :
    ∃ x, emptySlots L item n = .ok x := by
  obtain ⟨x, hx⟩ := defaultItems_ok hL h
  exact ⟨_, by simp [emptySlots, hx]; rfl⟩

theorem got_bag {a : Ty} (h : Got L (.bag a)) : Got L a ∧ (L.find? (.bag a)).isSome = true ∧
    (L.find? (.tuple [Ty.bool, a])).isSome = true :=
  ⟨⟨h.1.1, by simpa [Ty.sorted] using h.2⟩, h.1.2.2, h.1.2.1⟩

theorem got_list {a : Ty} (h : Got L (.list a)) : Got L a ∧ (L.find? (.list a)).isSome = true ∧
    (L.find? (.tuple [Ty.bool, a])).isSome = true :=
  ⟨⟨h.1.1, by simpa [Ty.sorted] using h.2⟩, h.1.2.2, h.1.2.1⟩

theorem got_table {k w : Ty} (h : Got L (.table k w)) : Got L k ∧ Got L w ∧ (L.find? (.table k w)).isSome = true ∧
    (L.find? (.tuple [Ty.bool, k, w])).isSome = true := by
  have hs := h.2
  simp only [Ty.sorted, Bool.and_eq_true] at hs
  exact ⟨⟨h.1.1, hs.1⟩, ⟨h.1.2.1, hs.2⟩, h.1.2.2.2, h.1.2.2.1⟩

theorem got_mems {D : Dsl → List Ty → Prop} (hD : D = Layout.HasDsl L) : {ts : List Ty} → Layout.HasWiths L D ts →
    Ty.sorteds ts = true → ∀ t ∈ ts, Got L t
  | _ :: _, ⟨h, _⟩, hs, _, .head _ => by
    subst hD; simp only [Ty.sorteds, Bool.and_eq_true] at hs; exact ⟨h, hs.1⟩
  | _ :: _, ⟨_, h⟩, hs, t, .tail _ ht => by
    simp only [Ty.sorteds, Bool.and_eq_true] at hs; exact got_mems hD h hs.2 t ht

theorem got_tuple {ts : List Ty} (h : Got L (.tuple ts)) : ∀ t ∈ ts, Got L t :=
  got_mems rfl h.1.1 (by simpa [Ty.sorted] using h.2)

theorem hasWithss_get {D : Dsl → List Ty → Prop} : {vs : List (List Ty)} → Layout.HasWithss L D vs →
    Ty.sortedss vs = true → (k : Fin vs.length) → Layout.HasWiths L D (vs.get k) ∧ Ty.sorteds (vs.get k) = true
  | _ :: _, ⟨h, _⟩, hs, ⟨0, _⟩ => by simp only [Ty.sortedss, Bool.and_eq_true] at hs; exact ⟨h, hs.1⟩
  | _ :: vs, ⟨_, h⟩, hs, ⟨k + 1, hk⟩ => by
    simp only [Ty.sortedss, Bool.and_eq_true] at hs
    exact hasWithss_get (vs := vs) h hs.2 ⟨k, by simpa using hk⟩

theorem got_adt {i : Nat} {a : List Ty} {vs : List (List Ty)} (h : Got L (.adt i a vs)) (k : Fin vs.length) :
    ∀ t ∈ vs.get k, Got L t := by
  match i, h with
  | 0, ⟨_, hs⟩ =>
    simp only [Ty.sorted, Option.isSome_iff_exists] at hs
    obtain ⟨⟨rfl⟩, -⟩ := hs
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ => simp
  | _ + 1, ⟨⟨hv, _⟩, hs⟩ =>
    have := hasWithss_get hv hs k
    exact got_mems rfl this.1 this.2

theorem collOf_sound (hL : SortedLayout L) {c : Ty} {item : List Ty} (S : List (Slot item.length)) (ha : Avail L c)
    (hf : L.Has c → (L.find? c).isSome = true ∧ (L.find? (.tuple (Ty.bool :: item))).isSome = true)
    (hi : Got L c → ∀ t ∈ item, Got L t) : Sound (fun _ => True) (collOf L c item S) := by
  unfold collOf
  refine sound_bind (collD_sound hL ha hf) fun r hr => ?_
  obtain ⟨x, hx⟩ := defaultItems_ok hL (hi hr.2)
  simp only [hx]; trivial

theorem listOf_sound (hL : SortedLayout L) {t : Ty} (items : List Term) (ha : Avail L (.list t)) :
    Sound (fun _ => True) (listOf L t items) := by
  unfold listOf
  refine sound_bind (collD_sound hL ha fun h => ⟨h.2.2, h.2.1⟩) fun r hr => ?_
  obtain ⟨x, hx⟩ := defaultE_ok hL (got_list hr.2).1
  simp only [hx]
  split <;> trivial

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem sound_need_limit {α : Type} {l : Limit} {o : Option α} : Sound (fun a => o = some a) (need (.limit l) o) :=
  sound_need fun _ => rfl

mutual
theorem encodePat_sound (hL : SortedLayout L) : {t : Ty} → {Δ : List Ty} → (p : Pat t Δ) → (s : Code t) →
    CodeOk L P ds H t s → Sound (fun r => CodesOk L P ds H Δ r.2) (encodePat L p s)
  | _, _, .wild, _, _ => trivial
  | _, _, .bind, _, h => ⟨h, trivial⟩
  | _, _, .int _, _, _ => trivial
  | _, _, .str lit, _, _ => by
    simp only [encodePat]; split
    · trivial
    · rfl
  | _, _, @Pat.tuple ts _ ps, s, h => by
    simp only [encodePat]
    refine sound_bind (tupleD_sound hL h) fun d hd => sound_bind sound_need_limit fun fs hfs => ?_
    exact encodePats_sound hL ps fs (codesOk_ofTerms hfs fun t ht => avail_of_got (got_tuple hd.2 t ht))
  | _, _, @Pat.ctor i args vs _ v ps, s, h => by
    simp only [encodePat]
    refine sound_bind (adtView_sound hL h v s) fun ⟨m, fts⟩ hv => sound_bind sound_need_limit fun fs hfs => ?_
    refine sound_bind (encodePats_sound hL ps fs (codesOk_ofTerms hfs fun t ht => avail_of_got (got_adt hv v t ht)))
      fun ⟨m', δ⟩ hδ => ?_
    exact hδ
  | _, _, .as p, s, h => by
    simp only [encodePat]
    exact sound_bind (encodePat_sound hL p s h) fun ⟨m, δ⟩ hδ => codesOk_append _ _ hδ ⟨h, trivial⟩
theorem encodePats_sound (hL : SortedLayout L) : {ts : List Ty} → {Δ : List Ty} → (ps : Pats ts Δ) → (ss : Codes ts) →
    CodesOk L P ds H ts ss → Sound (fun r => CodesOk L P ds H Δ r.2) (encodePats L ps ss)
  | _, _, .nil, (), _ => trivial
  | _, _, .cons p ps, (s, ss), ⟨h, hs⟩ => by
    simp only [encodePats]
    exact sound_bind (encodePat_sound hL p s h) fun ⟨m1, δ1⟩ h1 =>
      sound_bind (encodePats_sound hL ps ss hs) fun ⟨m2, δ2⟩ h2 => codesOk_append _ _ h1 h2
end

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem sound_termE {t : Ty} {c : Code t} : Sound (fun x => Code.term? t c = some x) (Code.termE t c) :=
  sound_need fun _ => rfl

theorem sound_mapM {α β : Type} {g : α → Except Refusal β} : (xs : List α) → (∀ x ∈ xs, Sound (fun _ => True) (g x)) →
    Sound (fun _ => True) (xs.mapM g)
  | [], _ => trivial
  | x :: xs, h => by
    rw [List.mapM_cons]
    exact sound_bind (h x (by simp)) fun _ _ =>
      sound_bind (sound_mapM xs fun y hy => h y (by simp [hy])) fun _ _ => trivial

theorem slotTerms_sound {ps : List Ty} {r : Ty} {w : Nat} {f : Code (.fn ps r)} (hf : CodeOk L P ds H (.fn ps r) f)
    (hps : ∀ t ∈ ps, Avail L t) (hr : Avail L r) (S : List (Slot w)) : Sound (fun _ => True) (slotTerms f S) := by
  unfold slotTerms
  refine sound_mapM S fun sl _ => ?_
  unfold slotApply
  refine sound_bind (sound_bind sound_need_limit fun xs hxs => hf xs (codesOk_ofTerms hxs hps) hr) fun _ _ => ?_
  exact sound_bind sound_termE fun _ _ => trivial

theorem slotTerms_sound1 {a r : Ty} {w : Nat} {f : Code (.fn [a] r)} (hf : CodeOk L P ds H (.fn [a] r) f)
    (ha : Got L a) (hr : Avail L r) (S : List (Slot w)) : Sound (fun _ => True) (slotTerms f S) :=
  slotTerms_sound hf (by simpa using avail_of_got ha) hr S

theorem slotTerms_sound2 {k v r : Ty} {w : Nat} {f : Code (.fn [k, v] r)} (hf : CodeOk L P ds H (.fn [k, v] r) f)
    (hk : Got L k) (hv : Got L v) (hr : Avail L r) (S : List (Slot w)) : Sound (fun _ => True) (slotTerms f S) :=
  slotTerms_sound hf (by simp [avail_of_got hk, avail_of_got hv]) hr S

theorem eqCode_sound (hL : SortedLayout L) {t : Ty} (x y : Code t) (hx : CodeOk L P ds H t x) :
    Sound (fun _ => True) (eqCode L t x y) := by
  unfold eqCode; split
  · exact sound_bind sound_termE fun _ _ => sound_bind sound_termE fun _ _ => trivial
  · split
    · rename_i a _ _
      exact sound_bind (collD_sound hL hx fun h => ⟨h.2.2, h.2.1⟩) fun _ _ => sound_mono (sound_need' rfl _ _) fun _ _ => trivial
    · rename_i k v _ _
      refine sound_bind (collD_sound hL hx fun h => ⟨h.2.2.2, h.2.2.1⟩) fun _ hr => ?_
      obtain ⟨dv, hdv⟩ := defaultE_ok hL (got_table hr.2).2.1
      simp only [hdv]
      exact sound_mono (sound_need' rfl _ _) fun _ _ => trivial
    · rfl

theorem encodeBin_sound (hL : SortedLayout L) {a b c : Ty} (op : BinOp a b c) (x : Code a) (y : Code b)
    (hx : CodeOk L P ds H a x) (hc : Avail L c) : Sound (fun r => CodeOk L P ds H c r) (encodeBin L op x y) := by
  cases op with
  | eq => exact sound_mono (eqCode_sound hL x y hx) fun _ _ => hc
  | ne => exact sound_bind (eqCode_sound hL x y hx) fun _ _ => hc
  | add | sub | mul | div | mod | lt | le | gt | ge | and | or | concat => exact hc

end

theorem SiteKey.same_self (a : SiteKey) : a.same a = true := by
  simp [SiteKey.same, Ty_sames_self]

theorem optSame_self {α : Type} {f : α → α → Bool} (hf : ∀ a, f a a = true) : (a : Option α) → optSame f a a = true
  | none => rfl
  | some a => hf a

theorem EffectKey.same_self (a : EffectKey) : a.same a = true := by
  have h1 := optSame_self (f := fun x y => (Ty.same x y).isSome) (fun t => Ty_same_self t) a.rejection
  have h2 := optSame_self SiteKey.same_self a.ensures
  simp [EffectKey.same, Ty_same_self, SiteKey.same_self, h1, h2]

theorem OwnKey.same_self (a : OwnKey) : a.same a = true := by
  cases a <;> simp [OwnKey.same, Ty_same_self, SiteKey.same_self]

/-- What a layout covers of a program with sites `P`, declarations `ds` and handles `H`: its datatypes and kinds have
sorts, and it has every kind of effect the program can make whose fields are data with sorts. -/
structure Covers (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite) : Prop where
  sorted : SortedLayout L
  requests : ∀ e, ∀ sh ∈ requestShapesAt ds e P, Ty.sorteds sh.key.fields = true →
    (Ty.tuple sh.key.fields).isData = true → sh.key ∈ L.effects
  commands : ∀ n r e c i j, (⟨"command", some n, [r, e, c, i, j]⟩ : HandleSite) ∈ H →
    ∀ s ∈ sitesOf P (Ty.fn [Ty.result Ty.nil j] (.list e)), Ty.sorteds [c, i, .tuple s.1] = true →
      (Ty.tuple [c, i, .tuple s.1]).isData = true → OwnKey.command e n c i j ⟨s.2.site, s.1⟩ ∈ L.owns
  queries : ∀ n r e c i o, (⟨"query", some n, [r, c, i, o]⟩ : HandleSite) ∈ H →
    ∀ s ∈ sitesOf P (Ty.fn [o] (.list e)), Ty.sorteds [c, i, .tuple s.1] = true →
      (Ty.tuple [c, i, .tuple s.1]).isData = true → OwnKey.query e n c i o ⟨s.2.site, s.1⟩ ∈ L.owns

section
variable {L : Layout}

theorem hasWithss_mem {D : Dsl → List Ty → Prop} : {vs : List (List Ty)} → Layout.HasWithss L D vs → ∀ fs ∈ vs,
    Layout.HasWiths L D fs
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, h⟩, fs, .tail _ hm => hasWithss_mem h fs hm

theorem tupleD_of_find {ts : List Ty} (h : (L.find? (.tuple ts)).isSome = true) : ∃ d, tupleD L ts = .ok d := by
  obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 h
  exact ⟨d, by simp [tupleD, hd]⟩

theorem lacksKind_gap {name : String} {fields : List Ty} (h : (lacksKind name fields).gap = true) :
    Ty.sorteds fields = true ∧ (Ty.tuple fields).isData = true := by
  unfold lacksKind at h
  split at h
  · cases h
  · split at h
    · rename_i h1 h2; simp at h1; exact ⟨h2, h1⟩
    · cases h

theorem mem_of_findIdx {α : Type} {p : α → Bool} {xs : List α} {k : Nat} (h : xs.findIdx? p = some k) :
    ∃ x ∈ xs, p x = true := by
  have : (xs.findIdx? p).isSome = true := by simp [h]
  simpa [List.findIdx?_isSome, List.any_eq_true] using this

/-- An effect of a kind the layout must have: its variant is found, else its fields are no data with sorts. -/
theorem effectT_sound (hL : SortedLayout L) (key : EffectKey) (input : Term) (ens answer : List Term)
    (he : Avail L (.dsl .effect [key.event]))
    (hk : Ty.sorteds key.fields = true → (Ty.tuple key.fields).isData = true → key ∈ L.effects) :
    Sound (fun _ => True) (effectT L key input ens answer) := by
  unfold effectT
  refine sound_bind (findE_sound hL he fun h => h.2) fun ⟨d, n⟩ hd => ?_
  refine sound_bind (sound_need fun hn => ?_) fun k hk' => ?_
  · cases hg : (lacksKind key.name key.fields).gap with
    | false => rfl
    | true =>
      obtain ⟨h1, h2⟩ := lacksKind_gap hg
      have hm : key ∈ L.effectsOf key.event := List.mem_filter.2 ⟨hk h1 h2, by simp [Ty_same_self]⟩
      have : ((L.effectsOf key.event).findIdx? (·.same key)).isSome = true := by
        simpa [List.findIdx?_isSome, List.any_eq_true] using ⟨key, hm, EffectKey.same_self key⟩
      simp [hn] at this
  · obtain ⟨x, hx, hxs⟩ := mem_of_findIdx hk'
    obtain rfl := EffectKey.eq_of_same hxs
    have hf : Layout.HasWiths L (fun _ _ => True) x.fields :=
      hasWithss_mem hd.2.1.1 _ (List.mem_append_left _ (List.mem_map_of_mem hx))
    obtain ⟨de, hde⟩ := tupleD_of_find hf.2.1.2
    obtain ⟨da, hda⟩ := tupleD_of_find hf.2.2.1.2
    simp only [hde, hda]; trivial

/-- An effect of an own kind the layout must have: its variant is found, else its fields are no data with sorts. -/
theorem ownT_sound (hL : SortedLayout L) (key : OwnKey) (caller input : Term) (answer : List Term)
    (he : Avail L (.dsl .effect [key.event]))
    (hk : Ty.sorteds key.fields = true → (Ty.tuple key.fields).isData = true → key ∈ L.owns) :
    Sound (fun _ => True) (ownT L key caller input answer) := by
  unfold ownT
  refine sound_bind (findE_sound hL he fun h => h.2) fun ⟨d, n⟩ hd => ?_
  refine sound_bind (sound_need fun hn => ?_) fun k hk' => ?_
  · cases hg : (lacksKind key.name key.fields).gap with
    | false => rfl
    | true =>
      obtain ⟨h1, h2⟩ := lacksKind_gap hg
      have hm : key ∈ L.ownsOf key.event := List.mem_filter.2 ⟨hk h1 h2, by simp [Ty_same_self]⟩
      have : ((L.ownsOf key.event).findIdx? (·.same key)).isSome = true := by
        simpa [List.findIdx?_isSome, List.any_eq_true] using ⟨key, hm, OwnKey.same_self key⟩
      simp [hn] at this
  · obtain ⟨x, hx, hxs⟩ := mem_of_findIdx hk'
    obtain rfl := OwnKey.eq_of_same hxs
    have hf : Layout.HasWiths L (fun _ _ => True) x.fields :=
      hasWithss_mem hd.2.1.1 _ (List.mem_append_right _ (List.mem_map_of_mem hx))
    have ha : (L.find? (.tuple x.answer.Γ)).isSome = true := by
      cases x <;> exact hf.2.2.1.2
    obtain ⟨da, hda⟩ := tupleD_of_find ha
    simp only [hda]; trivial

end

section
variable {P : List AnySite} {ds : List (String × DeclaredV)}

theorem declared_command {n : String} {a : List Ty} (hd : Declares ds ⟨"external command", some n, a⟩) :
    ∃ x i o j, (x, DeclaredV.externalCommand n i o j) ∈ ds ∧ a = [i, o, j] := by
  obtain ⟨n', hn, hany⟩ := hd
  obtain rfl : n = n' := Option.some.inj hn
  obtain ⟨⟨x, d⟩, hxd, hp⟩ := List.any_eq_true.1 hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hk, hn⟩, ht⟩ := hp
  cases d <;> simp [DeclaredV.kind] at hk
  rename_i n0 i o j
  simp only [DeclaredV.name] at hn; subst hn
  exact ⟨x, i, o, j, hxd, (eq_of_sames ht).symm⟩

theorem declared_query {n : String} {a : List Ty} (hd : Declares ds ⟨"external query", some n, a⟩) :
    ∃ x i o f, (x, DeclaredV.externalQuery n i o f) ∈ ds ∧ a = [i, o] := by
  obtain ⟨n', hn, hany⟩ := hd
  obtain rfl : n = n' := Option.some.inj hn
  obtain ⟨⟨x, d⟩, hxd, hp⟩ := List.any_eq_true.1 hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hk, hn⟩, ht⟩ := hp
  cases d <;> simp [DeclaredV.kind] at hk
  rename_i n0 i o f
  simp only [DeclaredV.name] at hn; subst hn
  exact ⟨x, i, o, f, hxd, (eq_of_sames ht).symm⟩

/-- A request to a declared external command with an `on_answer` the program writes is one of the request shapes. -/
theorem requestCommand_shape {n : String} {i o j e : Ty} {oa : ClosureCode}
    (hd : Declares ds ⟨"external command", some n, [i, o, j]⟩) (ho : ClosOk P (.fn [Ty.result o j] (.list e)) oa)
    (hdata : (Ty.tuple [i, .tuple [], .tuple oa.key.Γ]).isData = true) :
    ∃ sh ∈ requestShapesAt ds e P, sh.key = ⟨e, n, i, o, some j, none, oa.key⟩ := by
  obtain ⟨x, i', o', j', hx, he⟩ := declared_command hd
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨⟨site, Γ⟩, env⟩ := oa
  obtain ⟨⟨aΓ, a⟩, hs, hsite, hΓ⟩ := ho
  simp only at hsite hΓ hdata ⊢
  subst hsite hΓ
  refine ⟨⟨x, n, i, o, some j, none, aΓ, a, hdata⟩, ?_, rfl⟩
  simp only [requestShapesAt, List.mem_flatMap]
  refine ⟨_, hx, ?_⟩
  simp only [List.mem_filterMap]
  exact ⟨⟨aΓ, a⟩, hs, by simp [hdata]⟩

/-- A request to a declared external query with an `ensures` and an `on_answer` the program writes is one of the
request shapes. -/
theorem requestQuery_shape {n : String} {i o e : Ty} {ens oa : ClosureCode}
    (hd : Declares ds ⟨"external query", some n, [i, o]⟩) (hens : ClosOk P (.fn [i, o] Ty.rules) ens)
    (ho : ClosOk P (.fn [o] (.list e)) oa) (hdata : (Ty.tuple [i, .tuple ens.key.Γ, .tuple oa.key.Γ]).isData = true) :
    ∃ sh ∈ requestShapesAt ds e P, sh.key = ⟨e, n, i, o, none, some ens.key, oa.key⟩ := by
  obtain ⟨x, i', o', f, hx, he⟩ := declared_query hd
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨site, Γ⟩, env⟩ := oa
  obtain ⟨⟨esite, Γe⟩, eenv⟩ := ens
  obtain ⟨⟨aΓ, a⟩, hs, hsite, hΓ⟩ := ho
  obtain ⟨⟨eΓ, es⟩, hes, hesite, heΓ⟩ := hens
  simp only at hsite hΓ hdata hesite heΓ ⊢
  subst hsite hΓ hesite heΓ
  refine ⟨⟨x, n, i, o, none, some ⟨eΓ, es⟩, aΓ, a, hdata⟩, ?_, rfl⟩
  simp only [requestShapesAt, List.mem_flatMap]
  refine ⟨_, hx, ?_⟩
  exact List.mem_flatMap.2 ⟨⟨eΓ, es⟩, hes, List.mem_filterMap.2 ⟨⟨aΓ, a⟩, hs, by simp [hdata]⟩⟩

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem avail_bool : Avail L Ty.bool := fun _ => .inl rfl

theorem collD_bag (hL : SortedLayout L) {a : Ty} (h : Avail L (.bag a)) :
    Sound (fun r => L.find? (.bag a) = some (r.1, r.2.1) ∧ Got L (.bag a)) (collD L (.bag a) [a]) :=
  collD_sound hL h fun h => ⟨h.2.2, h.2.1⟩

theorem collD_list (hL : SortedLayout L) {a : Ty} (h : Avail L (.list a)) :
    Sound (fun r => L.find? (.list a) = some (r.1, r.2.1) ∧ Got L (.list a)) (collD L (.list a) [a]) :=
  collD_sound hL h fun h => ⟨h.2.2, h.2.1⟩

theorem collD_table (hL : SortedLayout L) {k v : Ty} (h : Avail L (.table k v)) :
    Sound (fun r => L.find? (.table k v) = some (r.1, r.2.1) ∧ Got L (.table k v)) (collD L (.table k v) [k, v]) :=
  collD_sound hL h fun h => ⟨h.2.2.2, h.2.2.1⟩

theorem lookupCode_sound (hL : SortedLayout L) {k v : Ty} (t key : Term) (h : Avail L (.table k v)) :
    Sound (fun _ => Got L (.table k v)) (lookupCode L k v t key) := by
  unfold lookupCode
  refine sound_bind (collD_table hL h) fun _ hr => sound_bind (sound_need' rfl _ _) fun _ _ => ?_
  obtain ⟨dv, hdv⟩ := defaultE_ok hL (got_table hr.2).2.1
  simp only [hdv]; exact hr.2

theorem pickCode_sound (hL : SortedLayout L) (lt : Term → Term → Term) {a : Ty} (b : Term) {f : Code (.fn [a] .int)}
    (hb : Avail L (.bag a)) (hf : CodeOk L P ds H (.fn [a] .int) f) (hr : Avail L (Ty.result a Ty.pickError)) :
    Sound (fun _ => True) (pickCode L lt a b f) := by
  unfold pickCode
  refine sound_bind (collD_bag hL hb) fun _ hc => ?_
  have ha := (got_bag hc.2).1
  refine sound_bind (slotTerms_sound1 hf ha avail_int _) fun _ _ => ?_
  obtain ⟨dv, hdv⟩ := defaultE_ok hL ha
  refine sound_bind_ok hdv ?_
  have hres : L.Has (Ty.result a Ty.pickError) :=
    hr (by simp [Ty.result, Ty.pickError, Ty.sorted, Ty.sorteds, Ty.sortedss, ha.2])
  have hpe : Avail L (.adt 4 [] [[], []]) := fun _ => hres.1.2.1.1
  refine sound_bind (adtCtor_sound hr _ _) fun _ _ => ?_
  refine sound_bind (adtCtor_sound hpe _ _) fun _ _ => sound_bind (adtCtor_sound hr _ _) fun _ _ => ?_
  refine sound_bind (adtCtor_sound hpe _ _) fun _ _ => sound_bind (adtCtor_sound hr _ _) fun _ _ => ?_
  trivial

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem avail_date : Avail L .date := fun _ => trivial

/-- The code of every built-in but the handle-making ones (which only a call with a literal name makes) has no gap
behind it. -/
theorem primCode_sound (hC : Covers L P ds H) (p : Prim) (args : List Ty) (h : p.ok args = true)
    (hp : handleOf p args none = none) :
    Sound (fun c => CodeOk L P ds H (p.ty.inst args) c) (primCode L p args h) := by
  have hL := hC.sorted
  match p, args, h with
  | .length, _, _ => intro _ _ _; exact avail_int
  | .dateAddDays, _, _ => intro _ _ _; exact avail_date
  | .dateDaysBetween, _, _ => intro _ _ _; exact avail_int
  | .require, args, _ =>
    intro ⟨holds, rej, next, ()⟩ ⟨_, _, hn, _⟩ hr
    exact sound_bind (hn () trivial hr) fun _ _ => sound_bind sound_termE fun _ _ =>
      sound_bind (adtCtor_sound hr _ _) fun _ _ => hr
  | .bagSize, args, _ =>
    intro ⟨b, ()⟩ ⟨hb, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ _ => avail_int
  | .bagFilter, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ hc =>
      sound_bind (slotTerms_sound1 hf (got_bag hc.2).1 avail_bool _) fun _ _ => hb
  | .bagCount, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ hc =>
      sound_bind (slotTerms_sound1 hf (got_bag hc.2).1 avail_bool _) fun _ _ => avail_int
  | .bagSum, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ hc =>
      sound_bind (slotTerms_sound1 hf (got_bag hc.2).1 avail_int _) fun _ _ => avail_int
  | .bagMap, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ hr
    refine sound_bind (collD_bag hL hb) fun _ hc => ?_
    have hr' : Avail L (.bag ((Ty.param 1).inst args)) := hr
    have hrb : Avail L ((Ty.param 1).inst args) := fun hs => (hr' (by simpa [Ty.sorted] using hs)).1
    exact sound_bind (slotTerms_sound1 hf (got_bag hc.2).1 hrb _) fun _ _ =>
      sound_bind (collOf_sound hL _ hr (fun h => ⟨h.2.2, h.2.1⟩) fun h => by simpa using (got_bag h).1) fun _ _ => hr
  | .bagAny, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ hc =>
      sound_bind (slotTerms_sound1 hf (got_bag hc.2).1 avail_bool _) fun _ _ => avail_bool
  | .bagAll, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ hc =>
      sound_bind (slotTerms_sound1 hf (got_bag hc.2).1 avail_bool _) fun _ _ => avail_bool
  | .bagInsert, args, _ =>
    intro ⟨b, x, ()⟩ ⟨hb, _, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ _ => sound_bind sound_termE fun _ _ => hb
  | .bagContains, args, _ =>
    intro ⟨b, x, ()⟩ ⟨hb, _, _⟩ _
    exact sound_bind (collD_bag hL hb) fun _ _ => sound_bind sound_termE fun _ _ =>
      sound_bind (sound_need' rfl _ _) fun _ _ => avail_bool
  | .bagMinBy, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ hr
    exact sound_mono (pickCode_sound hL _ b hb hf hr) fun _ _ => hr
  | .bagMaxBy, args, _ =>
    intro ⟨b, f, ()⟩ ⟨hb, hf, _⟩ hr
    exact sound_mono (pickCode_sound hL _ b hb hf hr) fun _ _ => hr
  | .tableNew, args, _ =>
    intro () _ hr
    refine sound_bind (collD_table hL hr) fun _ hc => ?_
    obtain ⟨S, hS⟩ := emptySlots_ok hL (item := [(Ty.param 0).inst args, (Ty.param 1).inst args]) (by
      have := got_table hc.2
      intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> first | exact this.1 | exact this.2.1) (_ : Nat)
    exact sound_bind_ok hS hr
  | .tableSize, args, _ =>
    intro ⟨t, ()⟩ ⟨ht, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ _ => avail_int
  | .tableFilter, args, _ =>
    intro ⟨t, f, ()⟩ ⟨ht, hf, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ hc =>
      sound_bind (slotTerms_sound2 hf (got_table hc.2).1 (got_table hc.2).2.1 avail_bool _) fun _ _ => ht
  | .tableMap, args, _ =>
    intro ⟨t, f, ()⟩ ⟨ht, hf, _⟩ hr
    refine sound_bind (collD_table hL ht) fun _ hc => ?_
    have hk := (got_table hc.2).1
    have hr' : Avail L (.table ((Ty.param 0).inst args) ((Ty.param 2).inst args)) := hr
    have hrw : Avail L ((Ty.param 2).inst args) := fun hs => (hr' (by simp [Ty.sorted, hk.2, hs])).2.1
    exact sound_bind (slotTerms_sound2 hf hk (got_table hc.2).2.1 hrw _) fun _ _ =>
      sound_bind (collOf_sound hL _ hr (fun h => ⟨h.2.2.2, h.2.2.1⟩)
        fun h => by have := got_table h; simp [this.1, this.2.1]) fun _ _ => hr
  | .tableKeys, args, _ =>
    intro ⟨t, ()⟩ ⟨ht, _⟩ hr
    exact sound_bind (collD_table hL ht) fun _ _ =>
      sound_mono (collOf_sound hL _ hr (fun h => ⟨h.2.2, h.2.1⟩) fun h => by simpa using (got_bag h).1) fun _ _ => hr
  | .tableValues, args, _ =>
    intro ⟨t, ()⟩ ⟨ht, _⟩ hr
    exact sound_bind (collD_table hL ht) fun _ _ =>
      sound_mono (collOf_sound hL _ hr (fun h => ⟨h.2.2, h.2.1⟩) fun h => by simpa using (got_bag h).1) fun _ _ => hr
  | .tableCount, args, _ =>
    intro ⟨t, f, ()⟩ ⟨ht, hf, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ hc =>
      sound_bind (slotTerms_sound2 hf (got_table hc.2).1 (got_table hc.2).2.1 avail_bool _) fun _ _ => avail_int
  | .tableAny, args, _ =>
    intro ⟨t, f, ()⟩ ⟨ht, hf, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ hc =>
      sound_bind (slotTerms_sound2 hf (got_table hc.2).1 (got_table hc.2).2.1 avail_bool _) fun _ _ => avail_bool
  | .tableAll, args, _ =>
    intro ⟨t, f, ()⟩ ⟨ht, hf, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ hc =>
      sound_bind (slotTerms_sound2 hf (got_table hc.2).1 (got_table hc.2).2.1 avail_bool _) fun _ _ => avail_bool
  | .tableRemove, args, _ =>
    intro ⟨t, key, ()⟩ ⟨ht, _, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ _ => sound_bind sound_termE fun _ _ =>
      sound_bind (sound_need' rfl _ _) fun _ _ => ht
  | .tableInsert, args, _ =>
    intro ⟨t, key, val, ()⟩ ⟨ht, _, _, _⟩ _
    exact sound_bind (collD_table hL ht) fun _ _ => sound_bind sound_termE fun _ _ =>
      sound_bind (sound_need' rfl _ _) fun _ _ => sound_bind sound_termE fun _ _ => ht
  | .bagFromList, args, _ =>
    intro ⟨items, ()⟩ ⟨hi, _⟩ hr
    exact sound_bind (collD_list hL hi) fun _ _ =>
      sound_mono (collOf_sound hL _ hr (fun h => ⟨h.2.2, h.2.1⟩) fun h => by simpa using (got_bag h).1) fun _ _ => hr
  | .tableFromList, args, _ =>
    intro ⟨pairs, ()⟩ ⟨hpr, _⟩ hr
    refine sound_bind (collD_table hL hr) fun _ hc => sound_bind (collD_list hL hpr) fun _ hl => ?_
    refine sound_bind (tupleD_sound hL (avail_of_got (got_list hl.2).1)) fun _ _ =>
      sound_bind (sound_need' rfl _ _) fun _ _ => ?_
    obtain ⟨S, hS⟩ := emptySlots_ok hL (item := [(Ty.param 0).inst args, (Ty.param 1).inst args]) (by
      have := got_table hc.2
      intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> first | exact this.1 | exact this.2.1) (_ : Nat)
    exact sound_bind_ok hS hr
  | .tableGet, args, _ =>
    intro ⟨t, key, ()⟩ ⟨ht, _, _⟩ hr
    exact sound_bind sound_termE fun _ _ => sound_bind (lookupCode_sound hL t _ ht) fun _ _ =>
      sound_bind (adtCtor_sound hr _ _) fun _ _ => sound_bind (adtCtor_sound hr _ _) fun _ _ => hr
  | .tableLookup, args, _ =>
    intro ⟨t, key, rej, next, ()⟩ ⟨ht, _, _, hn, _⟩ hr
    refine sound_bind sound_termE fun _ _ => sound_bind (lookupCode_sound hL t _ ht) fun _ hc => ?_
    refine sound_bind sound_need_limit fun fc hfc => ?_
    exact sound_bind (hn (fc, ()) ⟨codeOk_ofTerm hfc (avail_of_got (got_table hc).2.1), trivial⟩ hr) fun _ _ =>
      sound_bind sound_termE fun _ _ => sound_bind (adtCtor_sound hr _ _) fun _ _ => hr
  | .fresh, _, _ =>
    intro ⟨st, ix, ()⟩ _ hr
    exact sound_bind (findE_sound hL hr fun h => h) fun _ _ => hr
  | .externalCommand, _, _ | .externalQuery, _, _ | .command, _, _ | .query, _, _ => simp [handleOf] at hp
  | .requestCommand, args, _ =>
    intro ⟨name, input, oa, ()⟩ ⟨hn, _, ho, _⟩ hr
    refine sound_bind sound_termE fun it _ => sound_bind (effectT_sound hL _ it [] oa.env hr fun hs hd => ?_) fun _ _ => hr
    obtain ⟨sh, hsh, hk⟩ := requestCommand_shape hn ho hd
    rw [← hk] at hs hd ⊢
    exact hC.requests _ sh hsh hs hd
  | .requestQuery, args, _ =>
    intro ⟨⟨name, ens⟩, input, oa, ()⟩ ⟨⟨hn, he⟩, _, ho, _⟩ hr
    refine sound_bind sound_termE fun it _ =>
      sound_bind (effectT_sound hL _ it ens.env oa.env hr fun hs hd => ?_) fun _ _ => hr
    obtain ⟨sh, hsh, hk⟩ := requestQuery_shape hn he ho hd
    rw [← hk] at hs hd ⊢
    exact hC.requests _ sh hsh hs hd
  | .sendCommand, args, _ =>
    intro ⟨name, caller, input, oa, ()⟩ ⟨hn, _, _, ho, _⟩ hr
    refine sound_bind sound_termE fun _ _ => sound_bind sound_termE fun _ _ =>
      sound_bind (ownT_sound hL _ _ _ oa.env hr fun hs hd => ?_) fun _ _ => hr
    obtain ⟨s, hs', hsite, hΓ⟩ := ho
    obtain ⟨⟨site, Γ⟩, env⟩ := oa
    simp only at hsite hΓ hs hd ⊢
    subst hsite hΓ
    exact hC.commands name _ _ _ _ _ hn s hs' hs hd
  | .sendQuery, args, _ =>
    intro ⟨name, caller, input, oa, ()⟩ ⟨hn, _, _, ho, _⟩ hr
    refine sound_bind sound_termE fun _ _ => sound_bind sound_termE fun _ _ =>
      sound_bind (ownT_sound hL _ _ _ oa.env hr fun hs hd => ?_) fun _ _ => hr
    obtain ⟨s, hs', hsite, hΓ⟩ := ho
    obtain ⟨⟨site, Γ⟩, env⟩ := oa
    simp only at hsite hΓ hs hd ⊢
    subst hsite hΓ
    exact hC.queries name _ _ _ _ _ hn s hs' hs hd
  | .spec, _, _ | .service, _, _ | .machine, _, _ | .reaction, _, _ | .external, _, _ | .source, _, _
  | .declareCommand, _, _ | .declareQuery, _, _ | .declareSource, _, _ | .declareExternalCommand, _, _
  | .declareExternalQuery, _, _ | .subscribe, _, _ | .bounds, _, _ | .create, _, _ | .response, _, _
  | .scenario, _, _ | .stepCommand, _, _ | .stepQuery, _, _ | .stepWait, _, _ | .stepAnswerCommand, _, _
  | .stepAnswerQuery, _, _ | .stepEvent, _, _ | .fromMachine, _, _ | .fromReaction, _, _
  | .stepCommandThen, _, _ => rfl

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

/-- A handle the program makes is one `H` lists, with a literal name, and an external's is declared in `ds`. -/
def HandleOk (ds : List (String × DeclaredV)) (H : List HandleSite) (h : HandleSite) : Prop :=
  h ∈ H ∧ h.name.isSome = true ∧ (h.kind.startsWith "external" = true → Declares ds h)

theorem lit?_eq {G Γ : List Ty} {t : Ty} {e : Expr G Γ t} {n : String} (h : e.lit? = some n) :
    ∃ ht : t = .str, ht ▸ e = .str n := by
  cases e <;> simp [Expr.lit?] at h
  subst h; exact ⟨rfl, rfl⟩

theorem ok_length {p : Prim} {args : List Ty} (h : p.ok args = true) : args.length = p.sig.tvars.length := by
  simp only [Prim.ok, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1

/-- A call that makes a handle with a literal name, which check found declared or listed, codes it by that name. -/
theorem handleCall_sound {G Γ ps : List Ty} {r : Ty} (gs : Encs G) (σ : Codes Γ) (f : Expr G Γ (.fn ps r))
    (args : Exprs G Γ ps) {h : HandleSite} (hh : handleAt f args = some h) (hok : HandleOk ds H h)
    (hargs : Sound (fun p => CodesOk L P ds H ps p.1) (encodes L gs args σ)) :
    Sound (fun p => CodeOk L P ds H r p.1) (encode L gs (.call f args) σ) := by
  unfold handleAt at hh
  simp only at hh
  split at hh
  · rename_i p ts hp args
    cases p <;> try (simp [handleOf] at hh; done)
    case externalCommand =>
      rcases args with _ | ⟨e, rest⟩
      simp only [handleOf, Option.some.injEq] at hh
      subst hh
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hok.2.1
      obtain ⟨ht, he⟩ := lit?_eq hn
      have he' : e = Expr.str n := he
      subst he'
      have hlen := ok_length hp
      simp only [encode, encodes] at hargs ⊢
      cases hin : inDomain n
      · simp only [Bool.false_eq_true, ite_false]; rfl
      simp only [hin, ite_true, primCode, bind, Except.bind, pure, Except.pure] at hargs ⊢
      revert hargs
      generalize encodes L gs rest σ = X
      intro hargs
      cases X with
      | error => exact hargs
      | ok v =>
        match ts, hlen with
        | [_, _, _], _ => exact hok.2.2 (by simp)
    case externalQuery =>
      rcases args with _ | ⟨e, rest⟩
      simp only [handleOf, Option.some.injEq] at hh
      subst hh
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hok.2.1
      obtain ⟨ht, he⟩ := lit?_eq hn
      have he' : e = Expr.str n := he
      subst he'
      have hlen := ok_length hp
      simp only [encode, encodes] at hargs ⊢
      cases hin : inDomain n
      · simp only [Bool.false_eq_true, ite_false]; rfl
      simp only [hin, ite_true, primCode, bind, Except.bind, pure, Except.pure] at hargs ⊢
      revert hargs
      generalize encodes L gs rest σ = X
      intro hargs
      cases X with
      | error => exact hargs
      | ok v =>
        match ts, hlen with
        | [_, _], _ => exact ⟨hok.2.2 (by simp), hargs.2.1⟩
    case command =>
      rcases args with _ | ⟨e, rest⟩
      simp only [handleOf, Option.some.injEq] at hh
      subst hh
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hok.2.1
      obtain ⟨ht, he⟩ := lit?_eq hn
      have he' : e = Expr.str n := he
      subst he'
      have hlen := ok_length hp
      simp only [encode, encodes] at hargs ⊢
      cases hin : inDomain n
      · simp only [Bool.false_eq_true, ite_false]; rfl
      simp only [hin, ite_true, primCode, bind, Except.bind, pure, Except.pure] at hargs ⊢
      revert hargs
      generalize encodes L gs rest σ = X
      intro hargs
      cases X with
      | error => exact hargs
      | ok v =>
        match ts, hlen with
        | [_, _, _, _, _], _ => exact hok.1
    case query =>
      rcases args with _ | ⟨e, rest⟩
      simp only [handleOf, Option.some.injEq] at hh
      subst hh
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hok.2.1
      obtain ⟨ht, he⟩ := lit?_eq hn
      have he' : e = Expr.str n := he
      subst he'
      have hlen := ok_length hp
      simp only [encode, encodes] at hargs ⊢
      cases hin : inDomain n
      · simp only [Bool.false_eq_true, ite_false]; rfl
      simp only [hin, ite_true, primCode, bind, Except.bind, pure, Except.pure] at hargs ⊢
      revert hargs
      generalize encodes L gs rest σ = X
      intro hargs
      cases X with
      | error => exact hargs
      | ok v =>
        match ts, hlen with
        | [_, _, _, _], _ => exact hok.1
  · simp at hh

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem lacks_of_avail {t : Ty} (ha : Avail L t) (hn : L.find? t = none) (hf : L.Has t → (L.find? t).isSome = true) :
    (lacks t).gap = false := by
  cases hg : (lacks t).gap with
  | false => rfl
  | true => have := hf (ha (lacks_gap hg)); simp [hn] at this

theorem sitesOf_mem {Γ : List Ty} {t : Ty} {s : Site Γ t} (h : (⟨Γ, t, s⟩ : AnySite) ∈ P) : ⟨Γ, s⟩ ∈ sitesOf P t := by
  simp only [sitesOf, List.mem_filterMap]
  exact ⟨_, h, by simp [Ty_same_rfl]⟩

theorem codeOk_ite {r : Ty} {m : Term} {a b c : Code r} (h : Code.ite? r m a b = some c) (ha : CodeOk L P ds H r a) :
    CodeOk L P ds H r c := by
  simp only [Code.ite?, Option.bind_eq_bind] at h
  cases hx : Code.term? r a with
  | none => simp [hx] at h
  | some x =>
    cases hy : Code.term? r b with
    | none => simp [hx, hy] at h
    | some y =>
      simp only [hx, hy, Option.bind_some] at h
      exact codeOk_ofTerm h (avail_of_term hx ha)

theorem handleOf_name {p : Prim} {ts : List Ty} {h : HandleSite} (hh : handleOf p ts none = some h) : h.name = none := by
  cases p <;> simp [handleOf] at hh <;> subst hh <;> rfl

variable {G : List Ty} (D : Defs G) (gs : Encs G)

mutual
/-- The expression encoder meets no layout gap: in a layout that covers the program, an expression whose node types
are available, whose kept functions are the program's sites and whose handles check accepted has a code with no gap
behind it. -/
theorem encode_sound (hC : Covers L P ds H) (hgs : EncsOk L P ds H G gs) : {Γ : List Ty} → {t : Ty} → (e : Expr G Γ t) → (σ : Codes Γ) → CodesOk L P ds H Γ σ →
    (∀ u ∈ Expr.tys e, Avail L u) → (∀ s ∈ Expr.sites D e, s ∈ P) → (∀ h ∈ e.handles, HandleOk ds H h) →
    Sound (fun p => CodeOk L P ds H t p.1) (encode L gs e σ)
  | _, _, .int _, _, _, _, _, _ => avail_int
  | _, _, .str s, _, _, _, _, _ => by
    simp only [encode]; split
    · exact avail_str
    · rfl
  | _, _, .var v, σ, hσ, _, _, _ => codeOk_var v σ hσ
  | _, _, .global v, _, _, _, _, _ => encOk_var v gs hgs
  | _, _, .ctor v es, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encodes_sound hC hgs es σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun _ _ => sound_bind sound_need_limit fun _ _ => ?_
    exact sound_bind (adtCtor_sound (ht _ (by simp [Expr.tys])) _ _) fun _ _ => ht _ (by simp [Expr.tys])
  | _, _, @Expr.field _ _ i args vs ft _ k _ e, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun ⟨x, c⟩ hx => ?_
    rcases i with _ | i
    · rfl
    · simp only
      split
      · exact sound_bind sound_need_limit fun _ hc => codeOk_ofTerm hc (ht _ (by simp [Expr.tys]))
      · rename_i hn; exact lacks_of_avail hx hn fun h => h.2
  | _, _, @Expr.index _ _ ts e k, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun ⟨x, c⟩ hx => ?_
    exact sound_bind (tupleD_sound hC.sorted hx) fun _ _ =>
      sound_bind sound_need_limit fun _ hc => codeOk_ofTerm hc (ht _ (by simp [Expr.tys]))
  | _, _, @Expr.update _ _ i args fs e p, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm])))
      fun ⟨x, c⟩ hx => ?_
    rcases i with _ | i
    · rfl
    · simp only
      split
      · exact sound_bind (encodePatch_sound hC hgs p σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
          (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm]))
          (fun j => _) 0) fun _ _ => ht _ (by simp [Expr.tys])
      · rename_i hn; exact lacks_of_avail hx hn fun h => h.2
  | _, r, .call f args, σ, hσ, ht, hs, hh => by
    have hargs := encodes_sound hC hgs args σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h]))
      (fun h hm => hh h (by simp only [Expr.handles]; split <;> simp [hm]))
    cases hha : handleAt f args with
    | some h =>
      exact handleCall_sound gs σ f args hha (hh h (by simp [Expr.handles, hha])) hargs
    | none =>
      simp only [encode]
      refine sound_bind (encode_sound hC hgs f σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
        (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hha, hm])))
        fun ⟨sf, c1⟩ hf => sound_bind hargs fun ⟨ss, c2⟩ hss => ?_
      exact sound_bind (hf _ (codesOk_share _ _ hss) (ht r (by simp [Expr.tys]))) fun _ hr => hr
  | _, _, .lam body, σ, hσ, ht, hs, hh => by
    simp only [encode]
    intro xs hxs _
    exact encode_sound hC hgs body _ (codesOk_append xs σ hxs hσ) (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm))
  | _, _, .let_ e body, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm])))
      fun ⟨x, c⟩ hx => ?_
    exact sound_bind (encode_sound hC hgs body _ ⟨codeOk_share _ _ hx, hσ⟩ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm]))) fun _ hr => hr
  | _, _, .case e cs _, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm])))
      fun ⟨x, c⟩ hx => ?_
    refine sound_bind (encodeClauses_sound hC hgs cs σ hσ _ (codeOk_share _ _ hx) (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm]))) fun o ho => ?_
    cases o with
    | none => rfl
    | some p => obtain ⟨r, c2⟩ := p; exact ho (r, c2) rfl
  | _, _, .list items, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encodeItems_sound hC hgs items σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun ⟨ss, c⟩ _ => sound_bind (sound_mapM ss fun _ _ => sound_mono sound_termE fun _ _ => trivial) fun _ _ => ?_
    exact sound_bind (listOf_sound hC.sorted _ (ht _ (by simp [Expr.tys]))) fun _ _ => ht _ (by simp [Expr.tys])
  | _, _, .tuple es, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encodes_sound hC hgs es σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun _ _ => sound_bind sound_need_limit fun _ _ => ?_
    exact sound_bind (tupleD_sound hC.sorted (ht _ (by simp [Expr.tys]))) fun _ _ => ht _ (by simp [Expr.tys])
  | _, _, .bin op l r, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encode_sound hC hgs l σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm])))
      fun ⟨x, _⟩ hx => sound_bind (encode_sound hC hgs r σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
        (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm])))
      fun ⟨y, _⟩ _ => ?_
    exact sound_bind (encodeBin_sound hC.sorted op x y hx (ht _ (by simp [Expr.tys]))) fun _ hr => hr
  | _, _, .not e, σ, hσ, ht, hs, hh => by
    simp only [encode]
    exact sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun _ _ => avail_bool
  | _, _, .neg e, σ, hσ, ht, hs, hh => by
    simp only [encode]
    exact sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simpa [Expr.sites] using h)) (fun h hm => hh h (by simpa [Expr.handles] using hm)))
      fun _ _ => avail_int
  | _, _, .prim p args hp, _, _, _, _, hh => by
    simp only [encode]
    have hnone : handleOf p args none = none := by
      cases hx : handleOf p args none with
      | none => rfl
      | some x =>
        have := (hh x (by simp [Expr.handles, hx])).2.1
        simp [handleOf_name hx] at this
    exact sound_bind (primCode_sound hC p args hp hnone) fun _ hc => hc
  | _, _, @Expr.close _ _ Γ' t' site env hΓ' ht' body, σ, hσ, ht, hs, hh => by
    simp only [encode]
    refine sound_bind (encodes_sound hC hgs env σ hσ (fun u hu => ht u (by simp [Expr.tys, hu]))
      (fun s h => hs s (by simp [Expr.sites, h])) (fun h hm => hh h (by simp [Expr.handles, hm])))
      fun _ _ => sound_bind sound_need_limit fun _ _ => ?_
    exact ⟨_, sitesOf_mem (s := ⟨site, G, D, hΓ', ht', body⟩) (hs _ (by simp [Expr.sites])), rfl, rfl⟩
  | _, _, .closeEffect .., _, _, _, _, _ => rfl
theorem encodes_sound (hC : Covers L P ds H) (hgs : EncsOk L P ds H G gs) : {Γ : List Ty} → {ts : List Ty} → (es : Exprs G Γ ts) → (σ : Codes Γ) →
    CodesOk L P ds H Γ σ → (∀ u ∈ Exprs.tys es, Avail L u) → (∀ s ∈ Exprs.sites D es, s ∈ P) →
    (∀ h ∈ es.handles, HandleOk ds H h) → Sound (fun p => CodesOk L P ds H ts p.1) (encodes L gs es σ)
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .cons e es, σ, hσ, ht, hs, hh => by
    simp only [encodes]
    exact sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Exprs.tys, hu]))
      (fun s h => hs s (by simp [Exprs.sites, h])) (fun h hm => hh h (by simp [Exprs.handles, hm])))
      fun _ h1 => sound_bind (encodes_sound hC hgs es σ hσ (fun u hu => ht u (by simp [Exprs.tys, hu]))
        (fun s h => hs s (by simp [Exprs.sites, h])) (fun h hm => hh h (by simp [Exprs.handles, hm])))
      fun _ h2 => ⟨h1, h2⟩
theorem encodeItems_sound (hC : Covers L P ds H) (hgs : EncsOk L P ds H G gs) : {Γ : List Ty} → {t : Ty} → (es : Items G Γ t) → (σ : Codes Γ) →
    CodesOk L P ds H Γ σ → (∀ u ∈ Items.tys es, Avail L u) → (∀ s ∈ Items.sites D es, s ∈ P) →
    (∀ h ∈ es.handles, HandleOk ds H h) → Sound (fun _ => True) (encodeItems L gs es σ)
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .cons e es, σ, hσ, ht, hs, hh => by
    simp only [encodeItems]
    exact sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Items.tys, hu]))
      (fun s h => hs s (by simp [Items.sites, h])) (fun h hm => hh h (by simp [Items.handles, hm])))
      fun _ _ => sound_bind (encodeItems_sound hC hgs es σ hσ (fun u hu => ht u (by simp [Items.tys, hu]))
        (fun s h => hs s (by simp [Items.sites, h])) (fun h hm => hh h (by simp [Items.handles, hm])))
      fun _ _ => trivial
theorem encodePatch_sound (hC : Covers L P ds H) (hgs : EncsOk L P ds H G gs) : {Γ : List Ty} → {ts : List Ty} → (p : Patch G Γ ts) → (σ : Codes Γ) →
    CodesOk L P ds H Γ σ → (∀ u ∈ Patch.tys p, Avail L u) → (∀ s ∈ Patch.sites D p, s ∈ P) →
    (∀ h ∈ p.handles, HandleOk ds H h) → (keep : Nat → Term) → (j : Nat) →
    Sound (fun _ => True) (encodePatch L gs p σ keep j)
  | _, _, .nil, _, _, _, _, _, _, _ => trivial
  | _, _, .keep rest, σ, hσ, ht, hs, hh, keep, j => by
    simp only [encodePatch]
    exact sound_bind (encodePatch_sound hC hgs rest σ hσ (fun u hu => ht u (by simpa [Patch.tys] using hu))
      (fun s h => hs s (by simpa [Patch.sites] using h)) (fun h hm => hh h (by simpa [Patch.handles] using hm)) keep _)
      fun _ _ => trivial
  | _, _, .set e rest, σ, hσ, ht, hs, hh, keep, j => by
    simp only [encodePatch]
    exact sound_bind (encode_sound hC hgs e σ hσ (fun u hu => ht u (by simp [Patch.tys, hu]))
      (fun s h => hs s (by simp [Patch.sites, h])) (fun h hm => hh h (by simp [Patch.handles, hm])))
      fun _ _ => sound_bind sound_termE fun _ _ =>
        sound_bind (encodePatch_sound hC hgs rest σ hσ (fun u hu => ht u (by simp [Patch.tys, hu]))
          (fun s h => hs s (by simp [Patch.sites, h])) (fun h hm => hh h (by simp [Patch.handles, hm])) keep _)
        fun _ _ => trivial
theorem encodeClauses_sound (hC : Covers L P ds H) (hgs : EncsOk L P ds H G gs) : {Γ : List Ty} → {t r : Ty} → {sh : List Shape} → (cs : Clauses G Γ t r sh) →
    (σ : Codes Γ) → CodesOk L P ds H Γ σ → (s : Code t) → CodeOk L P ds H t s → (∀ u ∈ Clauses.tys cs, Avail L u) →
    (∀ x ∈ Clauses.sites D cs, x ∈ P) → (∀ h ∈ cs.handles, HandleOk ds H h) →
    Sound (fun o => ∀ p, o = some p → CodeOk L P ds H r p.1) (encodeClauses L gs cs σ s)
  | _, _, _, _, .nil, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | _, _, _, _, .cons p body rest, σ, hσ, s, hs0, ht, hs, hh => by
    simp only [encodeClauses]
    refine sound_bind (encodePat_sound hC.sorted p s hs0) fun ⟨m, δ⟩ hδ => ?_
    refine sound_bind (encode_sound hC hgs body _ (codesOk_append _ σ hδ hσ) (fun u hu => ht u (by simp [Clauses.tys, hu]))
      (fun x h => hs x (by simp [Clauses.sites, h])) (fun h hm => hh h (by simp [Clauses.handles, hm])))
      fun ⟨vb, cb⟩ hb => ?_
    refine sound_bind (encodeClauses_sound hC hgs rest σ hσ s hs0 (fun u hu => ht u (by simp [Clauses.tys, hu]))
      (fun x h => hs x (by simp [Clauses.sites, h])) (fun h hm => hh h (by simp [Clauses.handles, hm])))
      fun o _ => ?_
    cases o with
    | none => intro p hp; cases hp; exact hb
    | some q =>
      exact sound_bind sound_need_limit fun c hc => fun p hp => by cases hp; exact codeOk_ite hc hb
  | _, _, _, _, .guarded p g body rest, σ, hσ, s, hs0, ht, hs, hh => by
    simp only [encodeClauses]
    refine sound_bind (encodePat_sound hC.sorted p s hs0) fun ⟨m, δ⟩ hδ => ?_
    refine sound_bind (encode_sound hC hgs g _ (codesOk_append _ σ hδ hσ) (fun u hu => ht u (by simp [Clauses.tys, hu]))
      (fun x h => hs x (by simp [Clauses.sites, h])) (fun h hm => hh h (by simp [Clauses.handles, hm])))
      fun _ _ => ?_
    refine sound_bind (encode_sound hC hgs body _ (codesOk_append _ σ hδ hσ) (fun u hu => ht u (by simp [Clauses.tys, hu]))
      (fun x h => hs x (by simp [Clauses.sites, h])) (fun h hm => hh h (by simp [Clauses.handles, hm])))
      fun ⟨vb, cb⟩ hb => ?_
    refine sound_bind (encodeClauses_sound hC hgs rest σ hσ s hs0 (fun u hu => ht u (by simp [Clauses.tys, hu]))
      (fun x h => hs x (by simp [Clauses.sites, h])) (fun h hm => hh h (by simp [Clauses.handles, hm])))
      fun o _ => ?_
    cases o with
    | none => intro p hp; cases hp; exact hb
    | some q =>
      exact sound_bind sound_need_limit fun c hc => fun p hp => by cases hp; exact codeOk_ite hc hb
end

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

/-- Every global's code has no gap behind it, in a layout that covers the program: each body's node types are
available, its kept functions are sites of `P` and its handles are ones check accepted. -/
theorem Defs.encode_sound (hC : Covers L P ds H) : {G : List Ty} → (defs : Defs G) → (∀ u ∈ defs.tys, Avail L u) →
    (∀ s ∈ defs.sites, s ∈ P) → (∀ h ∈ defs.handles, HandleOk ds H h) → EncsOk L P ds H G (defs.encode L)
  | [], .nil, _, _, _ => trivial
  | _ :: _, .snoc defs _ body, ht, hs, hh => by
    have ih := Defs.encode_sound hC defs (fun u hu => ht u (by simp [Defs.tys, hu]))
      (fun s h => hs s (by simp [Defs.sites, h])) (fun h hm => hh h (by simp [Defs.handles, hm]))
    exact ⟨Tazuna.Smt.encode_sound defs (defs.encode L) hC ih body () trivial (fun u hu => ht u (by simp [Defs.tys, hu]))
      (fun s h => hs s (by simp [Defs.sites, h])) (fun h hm => hh h (by simp [Defs.handles, hm])), ih⟩

end

/-! The service's layout covers its program. -/

namespace Layout

/-- Every datatype of the layout has a sort, and its kinds of effect are `K`'s. -/
def AllSorted (K L : Layout) : Prop := (∀ p ∈ L.types, p.1.sorted = true) ∧ L.effects = K.effects ∧ L.owns = K.owns

theorem allSorted_push {K L : Layout} (h : AllSorted K L) {t : Ty} (ht : t.sorted = true) (n : Nat) :
    AllSorted K (L.push t n) := by
  unfold push; split
  · exact h
  · refine ⟨fun p hp => ?_, h.2⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact h.1 p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact ht

theorem sorteds_mem : {ts : List Ty} → Ty.sorteds ts = true → ∀ t ∈ ts, t.sorted = true
  | _ :: _, h, _, .head _ => by simp only [Ty.sorteds, Bool.and_eq_true] at h; exact h.1
  | _ :: _, h, t, .tail _ ht => by simp only [Ty.sorteds, Bool.and_eq_true] at h; exact sorteds_mem h.2 t ht

section
variable {slots : Ty → Nat} {dsl : Layout → Dsl → List Ty → Layout} {K : Layout}

mutual
theorem allSorted_addTyWith (hd : ∀ L k a, AllSorted K L → (Ty.dsl k a).sortable = true → AllSorted K (dsl L k a)) :
    (L : Layout) → AllSorted K L → (t : Ty) → t.sortable = true → AllSorted K (addTyWith slots dsl L t)
  | L, h, .tuple ts, ht => by
    have hs : Ty.sorteds ts = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact allSorted_push (allSorted_addTysWith hd L h ts fun t ht' => sortable_of_sorted t (sorteds_mem hs t ht'))
      (by simpa [Ty.sorted] using hs) _
  | L, h, .adt 0 a vs, ht => by
    simp only [addTyWith]; split
    · exact h
    · rename_i hb; simp [Ty.sortable, Ty.sorted, hb] at ht
  | L, h, .adt (i + 1) a vs, ht => by
    have hs : Ty.sortedss vs = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact allSorted_push (allSorted_addTyssWith hd L h vs hs) (by simpa [Ty.sorted] using hs) _
  | L, h, .id, _ => allSorted_push h rfl _
  | L, h, .list t, ht => by
    have hs : t.sorted = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact allSorted_push (allSorted_push (allSorted_addTyWith hd L h t (sortable_of_sorted t hs))
      (by simp [Ty.sorted, Ty.sorteds, Ty.bool, boolVs?, hs]) _) (by simpa [Ty.sorted] using hs) _
  | L, h, .bag t, ht => by
    have hs : t.sorted = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact allSorted_push (allSorted_push (allSorted_addTyWith hd L h t (sortable_of_sorted t hs))
      (by simp [Ty.sorted, Ty.sorteds, Ty.bool, boolVs?, hs]) _) (by simpa [Ty.sorted] using hs) _
  | L, h, .table k v, ht => by
    have hs : k.sorted = true ∧ v.sorted = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact allSorted_push (allSorted_push (allSorted_addTyWith hd _ (allSorted_addTyWith hd L h k
      (sortable_of_sorted k hs.1)) v (sortable_of_sorted v hs.2))
      (by simp [Ty.sorted, Ty.sorteds, Ty.bool, boolVs?, hs]) _) (by simp [Ty.sorted, hs]) _
  | L, h, .fn ps r, ht => by
    simp only [Ty.sortable, Bool.and_eq_true] at ht
    exact allSorted_addTyWith hd _ (allSorted_addTysWith hd L h ps (sortables_mem ht.1)) r ht.2
  | L, h, .dsl k a, ht => hd L k a h ht
  | _, h, .int, _ | _, h, .str, _ | _, h, .date, _ | _, h, .param _, _ => h
theorem allSorted_addTysWith (hd : ∀ L k a, AllSorted K L → (Ty.dsl k a).sortable = true → AllSorted K (dsl L k a)) :
    (L : Layout) → AllSorted K L → (ts : List Ty) → (∀ t ∈ ts, t.sortable = true) → AllSorted K (addTysWith slots dsl L ts)
  | _, h, [], _ => h
  | L, h, t :: ts, ht => allSorted_addTysWith hd _ (allSorted_addTyWith hd L h t (ht t (by simp))) ts
      fun t' h' => ht t' (by simp [h'])
theorem allSorted_addTyssWith (hd : ∀ L k a, AllSorted K L → (Ty.dsl k a).sortable = true → AllSorted K (dsl L k a)) :
    (L : Layout) → AllSorted K L → (vs : List (List Ty)) → Ty.sortedss vs = true → AllSorted K (addTyssWith slots dsl L vs)
  | _, h, [], _ => h
  | L, h, ts :: vs, hv => by
    simp only [Ty.sortedss, Bool.and_eq_true] at hv
    exact allSorted_addTyssWith hd _ (allSorted_addTysWith hd L h ts fun t ht => sortable_of_sorted t (sorteds_mem hv.1 t ht)) vs hv.2
theorem sortables_mem : {ts : List Ty} → Ty.sortables ts = true → ∀ t ∈ ts, t.sortable = true
  | _ :: _, h, _, .head _ => by simp only [Ty.sortables, Bool.and_eq_true] at h; exact h.1
  | _ :: _, h, t, .tail _ ht => by simp only [Ty.sortables, Bool.and_eq_true] at h; exact sortables_mem h.2 t ht
end

end

theorem allSorted_fold {K : Layout} (slots : Ty → Nat) : (fss : List (List Ty)) → (∀ fs ∈ fss, Ty.sorteds fs = true) →
    (L : Layout) → AllSorted K L → AllSorted K (fss.foldl (fun L fs => addTysWith slots (fun L _ _ => L) L fs) L)
  | [], _, _, h => h
  | fs :: fss, hf, L, h => allSorted_fold slots fss (fun fs' h' => hf fs' (by simp [h'])) _
      (allSorted_addTysWith (fun _ _ _ h _ => h) L h fs fun t ht => sortable_of_sorted t (sorteds_mem (hf fs (by simp)) t ht))

/-- The layout `addTys` builds from a layout without datatypes has only datatypes with sorts, given kinds whose
fields are data with sorts. -/
theorem allSorted_addTys (slots : Ty → Nat) (L : Layout) (hL : AllSorted L L)
    (hk : ∀ e, ∀ fs ∈ L.effectFields e, Ty.sorteds fs = true) (ts : List Ty) (hts : ∀ t ∈ ts, t.sortable = true) :
    AllSorted L (addTys slots L ts) := by
  unfold addTys
  refine allSorted_addTysWith ?_ L hL ts hts
  intro L' k a h' hka
  match k, a with
  | .effect, [e] =>
    show AllSorted L (addEffect _ L' e)
    have hf : L'.effectFields e = L.effectFields e := by
      simp [effectFields, effectsOf, ownsOf, h'.2.1, h'.2.2]
    exact allSorted_push (allSorted_fold _ _ (by rw [hf]; exact hk e) L' h') (by simpa [Ty.sortable, Ty.sorted] using hka) _
  | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
  | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
  | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
  | .closure, _ | .effectClosure, _ | .fresh, _ => exact h'

end Layout

theorem effectKey_same_iff (a b : EffectKey) : a.same b = true ↔ a = b :=
  ⟨EffectKey.eq_of_same, fun h => h ▸ EffectKey.same_self a⟩

theorem ownKey_same_iff (a b : OwnKey) : a.same b = true ↔ a = b :=
  ⟨OwnKey.eq_of_same, fun h => h ▸ OwnKey.same_self a⟩

theorem ty_same_iff (a b : Ty) : (Ty.same a b).isSome = true ↔ a = b :=
  ⟨eq_of_same, fun h => h ▸ Ty_same_self a⟩

theorem requestShapesAt_site {ds : List (String × DeclaredV)} {e : Ty} {P : List AnySite} {sh : RequestShape e}
    (h : sh ∈ requestShapesAt ds e P) : (⟨sh.answerΓ, _, sh.onAnswer⟩ : AnySite) ∈ P := by
  simp only [requestShapesAt, List.mem_flatMap] at h
  obtain ⟨⟨x, d⟩, -, hd⟩ := h
  cases d with
  | externalCommand n i o j =>
    simp only [List.mem_filterMap] at hd
    obtain ⟨⟨aΓ, a⟩, ha, hs⟩ := hd
    split at hs
    · cases hs; exact mem_sitesOf ha
    · cases hs
  | externalQuery n i o f =>
    dsimp only at hd
    obtain ⟨_, -, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨⟨aΓ, a⟩, ha, hs⟩ := List.mem_filterMap.1 hd
    split at hs
    · cases hs; exact mem_sitesOf ha
    · cases hs
  | command | query | source => simp at hd

theorem mem_eventTys {p : ProgramParts} {v : ServiceV} {Γ : List Ty} {u e : Ty} {s : Site Γ (.fn [u] (.list e))}
    (h : (⟨Γ, _, s⟩ : AnySite) ∈ p.sites) : e ∈ eventTys p v := by
  unfold eventTys
  rw [mem_dedupBy ty_same_iff]
  exact List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨_, h, rfl⟩)

/-- The service's layout covers its program: its datatypes and kinds have sorts, and it holds every kind of effect
the program can make whose fields are data with sorts. -/
theorem covers_ofParts (p : ProgramParts) (v : ServiceV) :
    Covers (Layout.ofParts p v) p.sites v.declared p.handles := by
  have hK : ∀ k ∈ (Layout.kindsOf p v).effects, Ty.sorteds k.fields = true ∧ (Ty.tuple k.fields).isData = true := by
    intro k hk
    simp only [Layout.kindsOf] at hk
    rw [mem_dedupBy effectKey_same_iff, List.mem_filter, Bool.and_eq_true] at hk
    exact hk.2
  have hO : ∀ k ∈ (Layout.kindsOf p v).owns, Ty.sorteds k.fields = true ∧ (Ty.tuple k.fields).isData = true := by
    intro k hk
    simp only [Layout.kindsOf] at hk
    rw [mem_dedupBy ownKey_same_iff, List.mem_filter, Bool.and_eq_true] at hk
    exact hk.2
  have hS := Layout.allSorted_addTys (listSlots (stepSlots v) p.lits) (Layout.kindsOf p v)
    ⟨(fun _ h => nomatch h), rfl, rfl⟩ (fun e fs hfs => by
      simp only [Layout.effectFields, Layout.effectsOf, Layout.ownsOf, List.mem_append, List.mem_map,
        List.mem_filter] at hfs
      rcases hfs with ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
      · exact (hK k hk).1
      · exact (hO k hk).1) ((stepTys v p.sites ++ p.tys ++ useTys v p.sites (Layout.kindsOf p v)).filter Ty.sortable)
      (fun t ht => (List.mem_filter.1 ht).2)
  have hE : (Layout.ofParts p v).effects = (Layout.kindsOf p v).effects := hS.2.1
  have hW : (Layout.ofParts p v).owns = (Layout.kindsOf p v).owns := hS.2.2
  refine ⟨⟨hS.1, fun k hk => hK k (hE ▸ hk), fun k hk => hO k (hW ▸ hk)⟩, ?_, ?_, ?_⟩
  · intro e sh hsh hs hd
    rw [hE]
    simp only [Layout.kindsOf]
    rw [mem_dedupBy effectKey_same_iff, List.mem_filter, Bool.and_eq_true]
    exact ⟨List.mem_flatMap.2 ⟨e, mem_eventTys (requestShapesAt_site hsh), List.mem_map_of_mem hsh⟩, hs, hd⟩
  · intro n r e c i j hh s hs hso hd
    rw [hW]
    simp only [Layout.kindsOf]
    rw [mem_dedupBy ownKey_same_iff, List.mem_filter, Bool.and_eq_true]
    refine ⟨List.mem_flatMap.2 ⟨_, hh, ?_⟩, hso, hd⟩
    simp only [ownKeys]
    exact List.mem_map.2 ⟨s, hs, rfl⟩
  · intro n r e c i o hh s hs hso hd
    rw [hW]
    simp only [Layout.kindsOf]
    rw [mem_dedupBy ownKey_same_iff, List.mem_filter, Bool.and_eq_true]
    refine ⟨List.mem_flatMap.2 ⟨_, hh, ?_⟩, hso, hd⟩
    simp only [ownKeys]
    exact List.mem_flatMap.2 ⟨e, mem_eventTys (mem_sitesOf hs), List.mem_map.2 ⟨s, hs, rfl⟩⟩

theorem handleOk_of_named {s : SpecV} {v : ServiceV} (hv : v ∈ s.services) {H : List HandleSite} {h : HandleSite}
    (hm : h ∈ H) (hn : h.Named s) : HandleOk v.declared H h := by
  obtain ⟨n, hname, hd⟩ := hn
  refine ⟨hm, by simp [hname], fun hx => ⟨n, hname, ?_⟩⟩
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at hd
  have := hd v hv
  simpa using this

/-- Every global of a checked spec's program has a code with no layout gap behind it in each service's layout: the
expression encoder, over every built-in, refuses only for the spec's reasons there. -/
theorem globals_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) :
    EncsOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles _
      (c.program.defs.encode (Layout.ofService c.program.defs v)) := by
  refine Defs.encode_sound (covers_ofParts c.program.defs.parts v) c.program.defs ?_ (fun _ h => h)
    (fun h hm => handleOk_of_named hv hm (c.handles h hm))
  intro u hu hs
  exact ofService_has c.program.defs v u
    (List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_append_right _ hu), sortable_of_sorted u hs⟩)

/-! Every site of the program is covered: its captured values' types, its body's node types, sites and handles are
the program's, over the definitions before its global. -/

section
variable {G : List Ty}

/-- A site of `D` whose captured types and body's node types are among `T`, whose body's sites are among `S` and
handles among `Hs`. -/
def Inside (D : Defs G) (T : List Ty) (S : List AnySite) (Hs : List HandleSite) (s : AnySite) : Prop :=
  (∀ u ∈ s.1, u ∈ T) ∧ (∀ u ∈ Expr.tys s.2.2.body, u ∈ T) ∧ (∀ x ∈ Expr.sites s.2.2.defs s.2.2.body, x ∈ S) ∧
    (∀ h ∈ Expr.handles s.2.2.body, h ∈ Hs) ∧ s.2.2.G = G ∧ HEq s.2.2.defs D

theorem Inside.mono {D : Defs G} {T T' : List Ty} {S S' : List AnySite} {Hs Hs' : List HandleSite} {s : AnySite}
    (h : Inside D T S Hs s) (hT : ∀ u ∈ T, u ∈ T') (hS : ∀ x ∈ S, x ∈ S') (hH : ∀ x ∈ Hs, x ∈ Hs') :
    Inside D T' S' Hs' s :=
  ⟨fun u hu => hT u (h.1 u hu), fun u hu => hT u (h.2.1 u hu), fun x hx => hS x (h.2.2.1 x hx),
    fun x hx => hH x (h.2.2.2.1 x hx), h.2.2.2.2⟩

theorem Expr.tys_head {Γ : List Ty} {t : Ty} (e : Expr G Γ t) : t ∈ Expr.tys e := by
  cases e <;> simp [Expr.tys]

theorem Exprs.tys_types : {Γ ts : List Ty} → (es : Exprs G Γ ts) → ∀ u ∈ ts, u ∈ Exprs.tys es
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons e es, u, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [Exprs.tys, Expr.tys_head e]
    · simp [Exprs.tys, Exprs.tys_types es u h]

theorem sites_of_handleAt {Γ ps : List Ty} {r : Ty} (D : Defs G) {f : Expr G Γ (.fn ps r)} {args : Exprs G Γ ps}
    {h : HandleSite} (hh : handleAt f args = some h) : Expr.sites D f = [] := by
  unfold handleAt at hh
  simp only at hh
  split at hh
  · rfl
  · simp at hh

/-- An effect site of `D` whose captured types and body's node types are among `T`, whose body's sites are among `S`
and handles among `Hs`. -/
def InsideE (D : Defs G) (T : List Ty) (S : List AnySite) (Hs : List HandleSite) (s : AnyEffectSite) : Prop :=
  (∀ u ∈ s.1, u ∈ T) ∧ (∀ u ∈ Expr.tys s.2.2.2.body, u ∈ T) ∧
    (∀ x ∈ Expr.sites s.2.2.2.defs s.2.2.2.body, x ∈ S) ∧ (∀ h ∈ Expr.handles s.2.2.2.body, h ∈ Hs) ∧
    s.2.2.2.G = G ∧ HEq s.2.2.2.defs D

theorem InsideE.mono {D : Defs G} {T T' : List Ty} {S S' : List AnySite} {Hs Hs' : List HandleSite}
    {s : AnyEffectSite} (h : InsideE D T S Hs s) (hT : ∀ u ∈ T, u ∈ T') (hS : ∀ x ∈ S, x ∈ S')
    (hH : ∀ x ∈ Hs, x ∈ Hs') : InsideE D T' S' Hs' s :=
  ⟨fun u hu => hT u (h.1 u hu), fun u hu => hT u (h.2.1 u hu), fun x hx => hS x (h.2.2.1 x hx),
    fun x hx => hH x (h.2.2.2.1 x hx), h.2.2.2.2⟩

theorem effectSites_of_handleAt {Γ ps : List Ty} {r : Ty} (D : Defs G) {f : Expr G Γ (.fn ps r)}
    {args : Exprs G Γ ps} {h : HandleSite} (hh : handleAt f args = some h) : Expr.effectSites D f = [] := by
  unfold handleAt at hh
  simp only at hh
  split at hh
  · rfl
  · simp at hh

variable (D : Defs G)

mutual
theorem Expr.inside : {Γ : List Ty} → {t : Ty} → (e : Expr G Γ t) → ∀ s ∈ Expr.sites D e,
    Inside D (Expr.tys e) (Expr.sites D e) (Expr.handles e) s
  | _, _, .int _, _, h | _, _, .str _, _, h | _, _, .var _, _, h | _, _, .global _, _, h | _, _, .prim .., _, h => by
    simp [Expr.sites] at h
  | _, _, .ctor _ es, s, h => (Exprs.inside es s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .tuple es, s, h => (Exprs.inside es s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .field _ _ _ e, s, h => (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .index e _, s, h => (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .not e, s, h => (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .neg e, s, h => (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .lam e, s, h => (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .list items, s, h => (Items.inside items s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .update e p, s, h => by
    simp only [Expr.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Patch.inside p s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .let_ e body, s, h => by
    simp only [Expr.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.inside body s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .bin _ l r, s, h => by
    simp only [Expr.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside l s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.inside r s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .case e cs _, s, h => by
    simp only [Expr.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside e s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Clauses.inside cs s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .call f args, s, h => by
    simp only [Expr.sites, List.mem_append] at h
    cases hha : handleAt f args with
    | some hd =>
      rcases h with h | h
      · rw [sites_of_handleAt D hha] at h; cases h
      · exact (Exprs.inside args s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
          (fun x hx => by simp [Expr.handles, hha, hx])
    | none =>
      rcases h with h | h
      · exact (Expr.inside f s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
          (fun x hx => by simp [Expr.handles, hha, hx])
      · exact (Exprs.inside args s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
          (fun x hx => by simp [Expr.handles, hha, hx])
  | _, _, @Expr.close _ _ Γ' t' site env hΓ ht body, s, h => by
    simp only [Expr.sites, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact ⟨fun u hu => by simp [Expr.tys, Exprs.tys_types env u hu], fun u hu => by simp [Expr.tys, hu],
        fun x hx => by simp [Expr.sites, hx], fun x hx => by simp [Expr.handles, hx], rfl, HEq.rfl⟩
    · exact (Exprs.inside env s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.inside body s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .closeEffect _ env _ _ body, s, h => by
    simp only [Expr.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Exprs.inside env s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.inside body s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
theorem Exprs.inside : {Γ ts : List Ty} → (es : Exprs G Γ ts) → ∀ s ∈ Exprs.sites D es,
    Inside D (Exprs.tys es) (Exprs.sites D es) (Exprs.handles es) s
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons e es, s, h => by
    simp only [Exprs.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside e s h).mono (fun u hu => by simp [Exprs.tys, hu]) (fun x hx => by simp [Exprs.sites, hx])
        (fun x hx => by simp [Exprs.handles, hx])
    · exact (Exprs.inside es s h).mono (fun u hu => by simp [Exprs.tys, hu]) (fun x hx => by simp [Exprs.sites, hx])
        (fun x hx => by simp [Exprs.handles, hx])
theorem Items.inside : {Γ : List Ty} → {t : Ty} → (es : Items G Γ t) → ∀ s ∈ Items.sites D es,
    Inside D (Items.tys es) (Items.sites D es) (Items.handles es) s
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons e es, s, h => by
    simp only [Items.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside e s h).mono (fun u hu => by simp [Items.tys, hu]) (fun x hx => by simp [Items.sites, hx])
        (fun x hx => by simp [Items.handles, hx])
    · exact (Items.inside es s h).mono (fun u hu => by simp [Items.tys, hu]) (fun x hx => by simp [Items.sites, hx])
        (fun x hx => by simp [Items.handles, hx])
theorem Patch.inside : {Γ ts : List Ty} → (p : Patch G Γ ts) → ∀ s ∈ Patch.sites D p,
    Inside D (Patch.tys p) (Patch.sites D p) (Patch.handles p) s
  | _, _, .nil, _, h => nomatch h
  | _, _, .keep rest, s, h => (Patch.inside rest s (by simpa [Patch.sites] using h)).mono
      (fun u hu => by simpa [Patch.tys] using hu) (fun x hx => by simpa [Patch.sites] using hx)
      (fun x hx => by simpa [Patch.handles] using hx)
  | _, _, .set e rest, s, h => by
    simp only [Patch.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside e s h).mono (fun u hu => by simp [Patch.tys, hu]) (fun x hx => by simp [Patch.sites, hx])
        (fun x hx => by simp [Patch.handles, hx])
    · exact (Patch.inside rest s h).mono (fun u hu => by simp [Patch.tys, hu]) (fun x hx => by simp [Patch.sites, hx])
        (fun x hx => by simp [Patch.handles, hx])
theorem Clauses.inside : {Γ : List Ty} → {t r : Ty} → {sh : List Shape} → (cs : Clauses G Γ t r sh) →
    ∀ s ∈ Clauses.sites D cs, Inside D (Clauses.tys cs) (Clauses.sites D cs) (Clauses.handles cs) s
  | _, _, _, _, .nil, _, h => nomatch h
  | _, _, _, _, .cons _ body rest, s, h => by
    simp only [Clauses.sites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.inside body s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
    · exact (Clauses.inside rest s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
  | _, _, _, _, .guarded _ g body rest, s, h => by
    simp only [Clauses.sites, List.mem_append] at h
    rcases h with (h | h) | h
    · exact (Expr.inside g s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
    · exact (Expr.inside body s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
    · exact (Clauses.inside rest s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
end

mutual
theorem Expr.insideE : {Γ : List Ty} → {t : Ty} → (e : Expr G Γ t) → ∀ s ∈ Expr.effectSites D e,
    InsideE D (Expr.tys e) (Expr.sites D e) (Expr.handles e) s
  | _, _, .int _, _, h | _, _, .str _, _, h | _, _, .var _, _, h | _, _, .global _, _, h | _, _, .prim .., _, h => by
    simp [Expr.effectSites] at h
  | _, _, .ctor _ es, s, h => (Exprs.insideE es s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .tuple es, s, h => (Exprs.insideE es s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .field _ _ _ e, s, h => (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .index e _, s, h => (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .not e, s, h => (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .neg e, s, h => (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .lam e, s, h => (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .list items, s, h => (Items.insideE items s h).mono (fun u hu => by simp [Expr.tys, hu])
      (fun x hx => by simpa [Expr.sites] using hx) (fun x hx => by simpa [Expr.handles] using hx)
  | _, _, .update e p, s, h => by
    simp only [Expr.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Patch.insideE p s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .let_ e body, s, h => by
    simp only [Expr.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.insideE body s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .bin _ l r, s, h => by
    simp only [Expr.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE l s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.insideE r s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .case e cs _, s, h => by
    simp only [Expr.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE e s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Clauses.insideE cs s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, .call f args, s, h => by
    simp only [Expr.effectSites, List.mem_append] at h
    cases hha : handleAt f args with
    | some hd =>
      rcases h with h | h
      · rw [effectSites_of_handleAt D hha] at h; cases h
      · exact (Exprs.insideE args s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
          (fun x hx => by simp [Expr.handles, hha, hx])
    | none =>
      rcases h with h | h
      · exact (Expr.insideE f s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
          (fun x hx => by simp [Expr.handles, hha, hx])
      · exact (Exprs.insideE args s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
          (fun x hx => by simp [Expr.handles, hha, hx])
  | _, _, .close _ env _ _ body, s, h => by
    simp only [Expr.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Exprs.insideE env s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.insideE body s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
  | _, _, @Expr.closeEffect _ _ Γ' ps r site env hΓ hps body, s, h => by
    simp only [Expr.effectSites, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact ⟨fun u hu => by simp [Expr.tys, Exprs.tys_types env u hu], fun u hu => by simp [Expr.tys, hu],
        fun x hx => by simp [Expr.sites, hx], fun x hx => by simp [Expr.handles, hx], rfl, HEq.rfl⟩
    · exact (Exprs.insideE env s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
    · exact (Expr.insideE body s h).mono (fun u hu => by simp [Expr.tys, hu]) (fun x hx => by simp [Expr.sites, hx])
        (fun x hx => by simp [Expr.handles, hx])
theorem Exprs.insideE : {Γ ts : List Ty} → (es : Exprs G Γ ts) → ∀ s ∈ Exprs.effectSites D es,
    InsideE D (Exprs.tys es) (Exprs.sites D es) (Exprs.handles es) s
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons e es, s, h => by
    simp only [Exprs.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE e s h).mono (fun u hu => by simp [Exprs.tys, hu]) (fun x hx => by simp [Exprs.sites, hx])
        (fun x hx => by simp [Exprs.handles, hx])
    · exact (Exprs.insideE es s h).mono (fun u hu => by simp [Exprs.tys, hu]) (fun x hx => by simp [Exprs.sites, hx])
        (fun x hx => by simp [Exprs.handles, hx])
theorem Items.insideE : {Γ : List Ty} → {t : Ty} → (es : Items G Γ t) → ∀ s ∈ Items.effectSites D es,
    InsideE D (Items.tys es) (Items.sites D es) (Items.handles es) s
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons e es, s, h => by
    simp only [Items.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE e s h).mono (fun u hu => by simp [Items.tys, hu]) (fun x hx => by simp [Items.sites, hx])
        (fun x hx => by simp [Items.handles, hx])
    · exact (Items.insideE es s h).mono (fun u hu => by simp [Items.tys, hu]) (fun x hx => by simp [Items.sites, hx])
        (fun x hx => by simp [Items.handles, hx])
theorem Patch.insideE : {Γ ts : List Ty} → (p : Patch G Γ ts) → ∀ s ∈ Patch.effectSites D p,
    InsideE D (Patch.tys p) (Patch.sites D p) (Patch.handles p) s
  | _, _, .nil, _, h => nomatch h
  | _, _, .keep rest, s, h => (Patch.insideE rest s (by simpa [Patch.effectSites] using h)).mono
      (fun u hu => by simpa [Patch.tys] using hu) (fun x hx => by simpa [Patch.sites] using hx)
      (fun x hx => by simpa [Patch.handles] using hx)
  | _, _, .set e rest, s, h => by
    simp only [Patch.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE e s h).mono (fun u hu => by simp [Patch.tys, hu]) (fun x hx => by simp [Patch.sites, hx])
        (fun x hx => by simp [Patch.handles, hx])
    · exact (Patch.insideE rest s h).mono (fun u hu => by simp [Patch.tys, hu]) (fun x hx => by simp [Patch.sites, hx])
        (fun x hx => by simp [Patch.handles, hx])
theorem Clauses.insideE : {Γ : List Ty} → {t r : Ty} → {sh : List Shape} → (cs : Clauses G Γ t r sh) →
    ∀ s ∈ Clauses.effectSites D cs, InsideE D (Clauses.tys cs) (Clauses.sites D cs) (Clauses.handles cs) s
  | _, _, _, _, .nil, _, h => nomatch h
  | _, _, _, _, .cons _ body rest, s, h => by
    simp only [Clauses.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact (Expr.insideE body s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
    · exact (Clauses.insideE rest s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
  | _, _, _, _, .guarded _ g body rest, s, h => by
    simp only [Clauses.effectSites, List.mem_append] at h
    rcases h with (h | h) | h
    · exact (Expr.insideE g s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
    · exact (Expr.insideE body s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
    · exact (Clauses.insideE rest s h).mono (fun u hu => by simp [Clauses.tys, hu])
        (fun x hx => by simp [Clauses.sites, hx]) (fun x hx => by simp [Clauses.handles, hx])
end

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

/-- The definitions are covered: their node types are available, their sites are `P`'s, their handles accepted. -/
def DefsOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite) {G : List Ty}
    (D : Defs G) : Prop :=
  (∀ u ∈ D.tys, Avail L u) ∧ (∀ x ∈ D.sites, x ∈ P) ∧ (∀ h ∈ D.handles, HandleOk ds H h)

/-- The site is covered: its captured types and body's node types are available, its body's sites are `P`'s and
handles accepted, and the definitions it sees are covered. -/
def SiteOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite) (s : AnySite) :
    Prop :=
  (∀ u ∈ s.1, Avail L u) ∧ (∀ u ∈ Expr.tys s.2.2.body, Avail L u) ∧ (∀ x ∈ Expr.sites s.2.2.defs s.2.2.body, x ∈ P) ∧
    (∀ h ∈ Expr.handles s.2.2.body, HandleOk ds H h) ∧ DefsOk L P ds H s.2.2.defs

/-- Every site of covered definitions is covered. -/
theorem siteOk_of : {G : List Ty} → (defs : Defs G) → DefsOk L P ds H defs → ∀ s ∈ defs.sites, SiteOk L P ds H s
  | [], .nil, _, _, h => nomatch h
  | _ :: _, .snoc defs _ body, ⟨ht, hs, hh⟩, s, h => by
    have hd : DefsOk L P ds H defs := ⟨fun u hu => ht u (by simp [Defs.tys, hu]),
      fun x hx => hs x (by simp [Defs.sites, hx]), fun x hx => hh x (by simp [Defs.handles, hx])⟩
    simp only [Defs.sites, List.mem_append] at h
    rcases h with h | h
    · exact siteOk_of defs hd s h
    · obtain ⟨hΓ, hb, hbs, hbh, hG, hD⟩ := Expr.inside defs body s h
      obtain ⟨Γ, t, ⟨site, G', D', hΓ', ht', b⟩⟩ := s
      simp only at hG hD hΓ hb hbs hbh ⊢
      subst hG
      obtain rfl := eq_of_heq hD
      exact ⟨fun u hu => ht u (by simp [Defs.tys, hΓ u hu]), fun u hu => ht u (by simp [Defs.tys, hb u hu]),
        fun x hx => hs x (by simp [Defs.sites, hbs x hx]), fun x hx => hh x (by simp [Defs.handles, hbh x hx]), hd⟩

/-- The effect site is covered, as `SiteOk` says of a site. -/
def EffectSiteOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    (s : AnyEffectSite) : Prop :=
  (∀ u ∈ s.1, Avail L u) ∧ (∀ u ∈ Expr.tys s.2.2.2.body, Avail L u) ∧
    (∀ x ∈ Expr.sites s.2.2.2.defs s.2.2.2.body, x ∈ P) ∧ (∀ h ∈ Expr.handles s.2.2.2.body, HandleOk ds H h) ∧
    DefsOk L P ds H s.2.2.2.defs

/-- Every effect site of covered definitions is covered. -/
theorem effectSiteOk_of : {G : List Ty} → (defs : Defs G) → DefsOk L P ds H defs → ∀ s ∈ defs.effectSites,
    EffectSiteOk L P ds H s
  | [], .nil, _, _, h => nomatch h
  | _ :: _, .snoc defs _ body, ⟨ht, hs, hh⟩, s, h => by
    have hd : DefsOk L P ds H defs := ⟨fun u hu => ht u (by simp [Defs.tys, hu]),
      fun x hx => hs x (by simp [Defs.sites, hx]), fun x hx => hh x (by simp [Defs.handles, hx])⟩
    simp only [Defs.effectSites, List.mem_append] at h
    rcases h with h | h
    · exact effectSiteOk_of defs hd s h
    · obtain ⟨hΓ, hb, hbs, hbh, hG, hD⟩ := Expr.insideE defs body s h
      obtain ⟨Γ, ps, r, ⟨site, G', D', hΓ', hps', b⟩⟩ := s
      simp only at hG hD hΓ hb hbs hbh ⊢
      subst hG
      obtain rfl := eq_of_heq hD
      exact ⟨fun u hu => ht u (by simp [Defs.tys, hΓ u hu]), fun u hu => ht u (by simp [Defs.tys, hb u hu]),
        fun x hx => hs x (by simp [Defs.sites, hbs x hx]), fun x hx => hh x (by simp [Defs.handles, hbh x hx]), hd⟩

theorem envCodes_ok : (Γ : List Ty) → (ρ : Ty.dens Γ) → (σ : Codes Γ) → envCodes L Γ ρ = some σ →
    (∀ u ∈ Γ, Avail L u) → CodesOk L P ds H Γ σ
  | [], (), (), _, _ => trivial
  | t :: Γ, (x, xs), (c, cs), h, ha => by
    cases hw : embedV L t x with
    | none => simp [envCodes, hw] at h
    | some w =>
      cases hc : Code.ofTerm? t w.term with
      | none => simp [envCodes, hw, hc] at h
      | some c' =>
        cases hcs : envCodes L Γ xs with
        | none => simp [envCodes, hw, hcs] at h
        | some cs' =>
          simp only [envCodes, hw, hc, hcs, Option.bind_some, Option.pure_def, bind] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨codeOk_ofTerm hc (ha t (by simp)), envCodes_ok Γ xs _ hcs fun u hu => ha u (by simp [hu])⟩

/-- A covered site's code over related captured values has no gap behind it. -/
theorem Site.code_sound (hC : Covers L P ds H) {Γ : List Ty} {t : Ty} (s : Site Γ t) (hs : SiteOk L P ds H ⟨Γ, t, s⟩)
    (σ : Codes Γ) (hσ : CodesOk L P ds H Γ σ) : Sound (fun p => CodeOk L P ds H t p.1) (s.code L σ) :=
  encode_sound s.defs (s.defs.encode L) hC (Defs.encode_sound hC s.defs hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2)
    s.body σ hσ hs.2.1 hs.2.2.1 hs.2.2.2.1

/-- A kept function at a covered site has a code with no gap behind it. -/
theorem Fun.code_sound (hC : Covers L P ds H) {t : Ty} (f : Fun t) (hs : SiteOk L P ds H f.asSite) :
    Sound (fun p => CodeOk L P ds H t p.1) (f.code L) := by
  unfold Fun.code
  refine sound_bind (sound_need fun _ => rfl) fun σ hσ => ?_
  exact encode_sound f.defs (f.defs.encode L) hC (Defs.encode_sound hC f.defs hs.2.2.2.2.1 hs.2.2.2.2.2.1
    hs.2.2.2.2.2.2) f.body σ (envCodes_ok _ _ σ hσ hs.1) hs.2.1 hs.2.2.1 hs.2.2.2.1

/-- A kept function that returns effects at a covered effect site has a code with no gap behind it. -/
theorem EffectFun.code_sound (hC : Covers L P ds H) {ps : List Ty} {r : Ty} (f : EffectFun ps r)
    (hs : EffectSiteOk L P ds H f.asSite) : Sound (fun p => CodeOk L P ds H (.fn ps r) p.1) (f.code L) := by
  unfold EffectFun.code
  refine sound_bind (sound_need fun _ => rfl) fun σ hσ => ?_
  exact encode_sound f.defs (f.defs.encode L) hC (Defs.encode_sound hC f.defs hs.2.2.2.2.1 hs.2.2.2.2.2.1
    hs.2.2.2.2.2.2) f.body σ (envCodes_ok _ _ σ hσ hs.1) hs.2.1 hs.2.2.1 hs.2.2.2.1

end

/-- Every site of a checked spec's program is covered in each service's layout, so a kept function at one of them,
and a pending request's `on_answer` and `ensures`, have codes with no layout gap behind them. -/
theorem sites_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) :
    ∀ s ∈ c.P, SiteOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles s :=
  siteOk_of c.program.defs ⟨fun u hu hs => ofService_has c.program.defs v u
    (List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_append_right _ hu), sortable_of_sorted u hs⟩), fun _ h => h,
    fun h hm => handleOk_of_named hv hm (c.handles h hm)⟩

/-- A kept function at a site of a checked spec's program has a code with no layout gap behind it in each service's
layout. -/
theorem Fun.code_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) {t : Ty} (f : Fun t)
    (hf : f.asSite ∈ c.P) :
    Sound (fun p => CodeOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles t p.1)
      (f.code (Layout.ofService c.program.defs v)) :=
  Fun.code_sound (covers_ofParts c.program.defs.parts v) f (sites_ofService c hv _ hf)

/-- A site of a checked spec's program, as a pending request's `on_answer` or `ensures` names one, has a code over
related captured values with no layout gap behind it in each service's layout. -/
theorem Site.code_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) {Γ : List Ty} {t : Ty}
    (s : Site Γ t) (hs : (⟨Γ, t, s⟩ : AnySite) ∈ c.P) (σ : Codes Γ)
    (hσ : CodesOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles Γ σ) :
    Sound (fun p => CodeOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles t p.1)
      (s.code (Layout.ofService c.program.defs v) σ) :=
  Site.code_sound (covers_ofParts c.program.defs.parts v) s (sites_ofService c hv _ hs) σ hσ

/-- A kept function that returns effects at an effect site of a checked spec's program has a code with no layout gap
behind it in each service's layout. -/
theorem EffectFun.code_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) {ps : List Ty} {r : Ty}
    (f : EffectFun ps r) (hf : f.asSite ∈ c.E) :
    Sound (fun p => CodeOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles (.fn ps r) p.1)
      (f.code (Layout.ofService c.program.defs v)) :=
  EffectFun.code_sound (covers_ofParts c.program.defs.parts v) f (effectSiteOk_of c.program.defs
    ⟨fun u hu hs => ofService_has c.program.defs v u
      (List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_append_right _ hu), sortable_of_sorted u hs⟩), fun _ h => h,
      fun h hm => handleOk_of_named hv hm (c.handles h hm)⟩ _ hf)

end Tazuna.Smt
