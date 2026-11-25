import Tazuna.Smt.EventMachines
import Tazuna.Semantics.PendingInv

/-! Writing an effect into the pending table. An effect value is coded by its kind's variant of the effect datatype
(`EffRel`); a pending request by its shape's variant of the pending entry (`PendingShape`). The shape of a request a
sender starts is fixed by the sender and the effect's kind: the kind names the request's types and the site ids of its
`on_answer` and `ensures`, and the external that lists the request (`RequestV.ownerIn`) depends only on the types. So
the encoder maps each kind to its shape statically (`shapeFor`), and the entry's fields are the effect variant's fields
with the sender's key in front (`entryT`). `entry_pending` proves the entry codes exactly the request the step writes,
because a closure that is a record of the program's unique sites is that site's record (`Fun.eq_siteFn`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout}

mutual
/-- On data, `RelD` at a value is `RelV` at the value read at the structure level. -/
theorem relD_up : (t : Ty) → (h : t.isData = true) → (y : t.den0) → (v : Val) → RelD L t y v →
    RelV L t (Ty.up t h y) v
  | .int, _, _, _, hv | .str, _, _, _, hv | .date, _, _, _, hv | .id, _, _, _, hv | .dsl .fresh _, _, _, _, hv => hv
  | .adt 0 a vs, h, y, v, hv => by
    obtain ⟨e, hv⟩ := hv
    subst e
    refine ⟨rfl, ?_⟩
    rw [hv]
    rcases y with u | u | u
    · erw [Ty.up_inl 0 a [] [[]] h rfl u]; rfl
    · erw [Ty.up_inr 0 a [] [[]] h rfl (.inl u), Ty.up_inl 0 a [] [] rfl rfl u]; rfl
    · exact u.elim
  | .adt (i + 1) a vs, h, y, v, ⟨d, n, hf, hr⟩ => ⟨d, n, hf, relDAlts_up d (i + 1) a 0 vs h y v hr⟩
  | .tuple ts, h, y, v, ⟨d, n, vals, hf, hv, hr⟩ => ⟨d, n, vals, hf, hv, relDs_up ts h y vals hr⟩
  | .bag t, h, xs, v, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys, hp, hh⟩ => by
    have ht : t.isData = true := by simpa [Ty.isData] using h
    rw [Ty.up_bag t h ht]
    exact ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys.map (Ty.up t ht), hp.map _,
      forall2_map _ (fun y vs ⟨z, hz, hyz⟩ => ⟨z, hz, relD_up t ht _ z hyz⟩) hh⟩
  | .list t, h, xs, v, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, hh⟩ => by
    have ht : t.isData = true := by simpa [Ty.isData] using h
    rw [Ty.up_list t h ht]
    exact ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5,
      forall2_map _ (fun y vs ⟨z, hz, hyz⟩ => ⟨z, hz, relD_up t ht _ z hyz⟩) hh⟩
  | .table k w, h, x, v, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys, hp, hh⟩ => by
    have h' := h
    simp only [Ty.isData, Bool.and_eq_true] at h'
    have hk : k.isData = true := h'.1
    have hw : w.isData = true := h'.2
    let up : k.den0 × w.den0 → k.den × w.den := fun p => (Ty.up k hk p.1, Ty.up w hw p.2)
    refine ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys.map up, ?_, ?_⟩
    · rw [Ty.up_table k w h hk hw]; exact hp.map _
    · exact forall2_map up (fun e vs ⟨zk, zv, hz, h1, h2⟩ =>
        ⟨zk, zv, hz, relD_up k hk _ zk h1, relD_up w hw _ zv h2⟩) hh
  | .fn .., _, _, _, hv | .param _, _, _, _, hv => hv.elim
  | .dsl .effect _, h, _, _, _ => by simp [Ty.isData] at h
  | .dsl .spec _, _, _, _, hv | .dsl .service _, _, _, _, hv | .dsl .command _, _, _, _, hv
  | .dsl .query _, _, _, _, hv | .dsl .machine _, _, _, _, hv | .dsl .reaction _, _, _, _, hv
  | .dsl .external _, _, _, _, hv | .dsl .externalCommand _, _, _, _, hv | .dsl .externalQuery _, _, _, _, hv
  | .dsl .source _, _, _, _, hv | .dsl .declared _, _, _, _, hv | .dsl .subscription _, _, _, _, hv
  | .dsl .bounds _, _, _, _, hv | .dsl .create _, _, _, _, hv | .dsl .response _, _, _, _, hv
  | .dsl .scenario _, _, _, _, hv | .dsl .step _, _, _, _, hv | .dsl .sender _, _, _, _, hv
  | .dsl .closure _, _, _, _, hv | .dsl .effectClosure _, _, _, _, hv => by simp [RelD] at hv
theorem relDs_up : (ts : List Ty) → (h : (Ty.tuple ts).isData = true) → (y : (Ty.semsWith Dsl.base ts).1) →
    (vals : List Val) → RelDs L ts y vals → RelVs L ts (Ty.up (.tuple ts) h y) vals
  | [], _, _, _, hv => hv
  | t :: ts, h, y, vals, hv => by
    have h' := h
    simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h'
    have ht : t.isData = true := h'.1
    have hts : (Ty.tuple ts).isData = true := by simpa [Ty.isData] using h'.2
    erw [Ty.up_tuple t ts h ht hts]
    obtain ⟨v, vs, e, h1, h2⟩ := hv
    exact ⟨v, vs, e, relD_up t ht y.1 v h1, relDs_up ts hts y.2 vs h2⟩
theorem relDAlts_up (d i : Nat) (a : List Ty) : (k : Nat) → (vs : List (List Ty)) → (h : (Ty.adt i a vs).isData = true) →
    (y : (Ty.semAltsWith Dsl.base vs).1) → (v : Val) → RelDAlts L d k vs y v →
    RelAlts L d k vs (Ty.up (.adt i a vs) h y) v
  | _, [], _, y, _, _ => nomatch y
  | k, fs :: vs, h, .inl x, v, hv => by
    have h' := h
    simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at h'
    have hfs : (Ty.tuple fs).isData = true := by simpa [Ty.isData] using h'.1
    erw [Ty.up_inl i a fs vs h hfs x]
    obtain ⟨vals, e, hr⟩ := hv
    exact ⟨vals, e, relDs_up fs hfs x vals hr⟩
  | k, fs :: vs, h, .inr y, v, hv => by
    have h' := h
    simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at h'
    have hvs : (Ty.adt i a vs).isData = true := by simpa [Ty.isData] using h'.2
    erw [Ty.up_inr i a fs vs h hvs y]
    exact relDAlts_up d i a (k + 1) vs hvs y v hv
end

end

theorem eq_of_same {a b : Ty} (h : (Ty.same a b).isSome = true) : a = b := by
  obtain ⟨⟨e⟩, -⟩ := Option.isSome_iff_exists.1 h; exact e

theorem eq_of_sames {a b : List Ty} (h : (Ty.sames a b).isSome = true) : a = b := by
  obtain ⟨⟨e⟩, -⟩ := Option.isSome_iff_exists.1 h; exact e

section
variable {e : Ty} {L : Layout}

/-- The sites a shape names are sites of `P`. -/
def _root_.Tazuna.Ir.PendingShape.InSites (P : List AnySite) (sh : PendingShape e) : Prop :=
  (⟨sh.answerΓ, _, sh.onAnswer⟩ : AnySite) ∈ P ∧ ∀ s ∈ sh.ensures, (⟨s.1, _, s.2⟩ : AnySite) ∈ P

theorem mem_sitesOf {sites : List AnySite} {t : Ty} {Γ : List Ty} {s : Site Γ t} (h : ⟨Γ, s⟩ ∈ sitesOf sites t) :
    (⟨Γ, t, s⟩ : AnySite) ∈ sites := by
  simp only [sitesOf, List.mem_filterMap] at h
  obtain ⟨⟨Γ', u, s'⟩, hm, hs⟩ := h
  cases hu : Ty.same u t with
  | none => rw [hu] at hs; cases hs
  | some p =>
    obtain ⟨e⟩ := p
    subst e
    rw [hu] at hs
    simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at hs
    obtain ⟨rfl, hs⟩ := hs
    cases hs
    exact hm

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- Every shape a service's states can hold names sites of the program. -/
theorem shapes_inSites {v : ServiceV} {P : List AnySite} {sh : PendingShape v.event} (h : sh ∈ shapes v P) :
    sh.InSites P := by
  simp only [shapes, List.mem_flatMap] at h
  obtain ⟨⟨ks, snd⟩, -, h⟩ := h
  split at h
  · simp only [List.mem_map] at h
    obtain ⟨rq, hrq, rfl⟩ := h
    simp only [requestShapes, List.mem_flatMap] at hrq
    obtain ⟨⟨x, d⟩, -, hrq⟩ := hrq
    have hmk : ∀ (name : String) (i o : Ty) (j : Option Ty)
        (ens : Option ((Γ : List Ty) × Site Γ (Ty.fn [i, answerTy o j] Ty.rules))),
        (∀ s ∈ ens, (⟨s.1, _, s.2⟩ : AnySite) ∈ P) → ∀ rq' ∈ ((sitesOf P (Ty.fn [answerTy o j] (.list v.event))).filterMap
          fun (⟨aΓ, a⟩ : (Γ : List Ty) × Site Γ _) =>
          if h : (Ty.tuple [i, .tuple ((ens.map (·.1)).getD []), .tuple aΓ]).isData = true then
            some (⟨x, name, i, o, j, ens, aΓ, a, h⟩ : RequestShape v.event) else none),
        (⟨rq'.answerΓ, _, rq'.onAnswer⟩ : AnySite) ∈ P ∧ ∀ s ∈ rq'.ensures, (⟨s.1, _, s.2⟩ : AnySite) ∈ P := by
      intro name i o j ens hens rq' hrq'
      simp only [List.mem_filterMap] at hrq'
      obtain ⟨⟨aΓ, a⟩, ha, hrq'⟩ := hrq'
      split at hrq'
      · cases hrq'; exact ⟨mem_sitesOf ha, hens⟩
      · cases hrq'
    split at hrq
    · exact hmk _ _ _ _ none (by intro s hs; cases hs) rq hrq
    · obtain ⟨es, hes, hrq⟩ := List.mem_flatMap.1 hrq
      exact hmk _ _ _ none (some es) (by
        intro s hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs; exact mem_sitesOf hes) rq hrq
    · cases hrq
  · cases h

/-- Whether a site is the one a kept function's code names. -/
def siteMatch {Γ : List Ty} {t : Ty} (s : Site Γ t) (k : SiteKey) : Bool :=
  s.site == k.site && (Ty.sames Γ k.Γ).isSome

/-- Whether two sender shapes are the same. -/
def senderSame {ks ks' : List Ty} : SenderShape ks → SenderShape ks' → Bool
  | .machine n k, .machine n' k' => n == n' && (Ty.same k k').isSome
  | .reaction n, .reaction n' => n == n'
  | _, _ => false

theorem senderSame_eq : {ks ks' : List Ty} → (a : SenderShape ks) → (b : SenderShape ks') → senderSame a b = true →
    (⟨ks, a⟩ : (ks : List Ty) × SenderShape ks) = ⟨ks', b⟩
  | _, _, .machine n k, .machine n' k', h => by
    simp only [senderSame, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hk⟩ := h
    obtain rfl := eq_of_same hk
    rfl
  | _, _, .reaction n, .reaction n', h => by
    simp only [senderSame, beq_iff_eq] at h
    subst h
    rfl
  | _, _, .machine _ _, .reaction _, h | _, _, .reaction _, .machine _ _, h => by simp [senderSame] at h

/-- Whether a shape is the one a request of the effect kind `key` takes when the sender `snd` starts it and the
external `x` lists it. -/
def _root_.Tazuna.Ir.PendingShape.fits (sh : PendingShape e) (snd : (ks : List Ty) × SenderShape ks) (key : EffectKey)
    (x : String) : Bool :=
  senderSame sh.sender snd.2 &&
  sh.external == x && sh.name == key.name && (Ty.same sh.input key.input).isSome &&
  (Ty.same sh.output key.output).isSome && optSame (fun a b => (Ty.same a b).isSome) sh.rejection key.rejection &&
  (match sh.ensures, key.ensures with
    | none, none => true
    | some ⟨_, s⟩, some k => siteMatch s k
    | _, _ => false) &&
  siteMatch sh.onAnswer key.answer

/-- The external a request of the kind goes to: `RequestV.ownerIn` reads only the kind's name and types. -/
def _root_.Tazuna.Smt.EffectKey.owner (key : EffectKey) (ds : List (String × DeclaredV)) : Option String :=
  let same (a b : Ty) := (Ty.same a b).isSome
  (ds.find? fun (_, d) => match d, key.rejection with
    | .externalCommand n i o j, some j' => n == key.name && same i key.input && same o key.output && same j j'
    | .externalQuery n i o _, none => n == key.name && same i key.input && same o key.output
    | _, _ => false).map (·.1)

theorem owner_eq {key : EffectKey} {r : RequestV e} {vals : List Val} (h : key.Holds L (.request r) vals)
    (ds : List (String × DeclaredV)) : r.ownerIn ds = key.owner ds := by
  obtain ⟨name, input, output, rej, value, ens, onA⟩ := r
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  dsimp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- A machine's key as its sender's key tuple. -/
theorem machineKey_rel {r e : Ty} (m : MachineV r e) (k : m.key.den0) {zk : Val}
    (hzk : RelV L m.key (Ty.up _ m.key_data k) zk) {dk nk : Nat} (hdk : L.find? (.tuple [m.key]) = some (dk, nk)) :
    RelD L (.tuple [m.key]) (k, ()) (.ctor dk 0 [zk]) :=
  ⟨dk, nk, [zk], hdk, rfl, zk, [], rfl, relV_up _ _ _ _ hzk, rfl⟩

theorem fits_pending {P : List AnySite} (hP : SitesUnique P) {e : Ty} {sh : PendingShape e}
    (hsh : sh.InSites P) {ks : List Ty} {sd : SenderShape ks} {key : EffectKey} {x : String}
    (hfit : sh.fits ⟨ks, sd⟩ key x = true)
    {req : RequestV e} (hreach : (EffectV.request req).Reach P) {vals : List Val}
    (hh : key.Holds L (.request req) vals) (kv : (Ty.tuple ks).den0) {zkv : Val}
    (hK : RelD L (.tuple ks) kv zkv) (id : Nat) :
    ∃ fx : Ty.dens sh.fields, RelVs L sh.fields fx (zkv :: vals) ∧
      sh.pending id fx = ⟨id, sd.sender kv, x, req⟩ := by
  obtain ⟨⟨ext, name, input, output, rej, ens, aΓ, onA, hf⟩, ks0, snd, hks⟩ := sh
  obtain ⟨rname, rinput, routput, rrej, rvalue, rens, ronA⟩ := req
  obtain ⟨kev, kname, kinput, koutput, krej, kens, ⟨ksite, kΓ⟩⟩ := key
  obtain ⟨rs, rG, rdefs, rΓ, renv, rhΓ, rht, rbody⟩ := ronA
  obtain ⟨h1, h2, h3, h4, h5, h6, vi, ve, va, rfl, hvi, hva, hens⟩ := hh
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4
  simp only [PendingShape.fits, Bool.and_eq_true, beq_iff_eq, siteMatch] at hfit
  obtain ⟨⟨⟨⟨⟨⟨⟨hsnd, rfl⟩, rfl⟩, hin⟩, hout⟩, hrej⟩, hensm⟩, hans1, hans2⟩ := hfit
  cases senderSame_eq snd sd hsnd
  · obtain rfl := eq_of_same hin
    obtain rfl := eq_of_same hout
    have hrj : rej = rrej := by
      cases rej <;> cases rrej <;> simp only [optSame, reduceCtorEq] at hrej ⊢
      exact congrArg some (eq_of_same hrej)
    subst hrj
    subst h5 h6 hans1
    obtain rfl := eq_of_sames hans2
    dsimp only at hvi hva hens hreach
    obtain ⟨hrA, hrE, -, -⟩ := hreach
    obtain ⟨hsA, hsE⟩ := hsh
    obtain ⟨⟨⟩, hA⟩ := Fun.eq_siteFn hP _ onA hrA hsA rfl
    cases rens with
    | none =>
      cases kens with
      | some _ => exact hens.elim
      | none =>
        cases ens with
        | some _ => simp at hensm
        | none =>
          obtain ⟨d0, n0, hd0, rfl⟩ := hens
          refine ⟨Ty.up (.tuple _) (PendingShape.hdata _) (kv, rvalue, (), renv, ()),
            relDs_up _ _ _ _ ⟨_, _, rfl, hK, _, _, rfl, hvi, _, _, rfl, ⟨d0, n0, [], hd0, rfl, rfl⟩, _, _, rfl, hva, rfl⟩,
            ?_⟩
          simp only [PendingShape.pending]
          erw [Ty.down_up]
          dsimp only at hA
          rw [hA]
          rfl
    | some f =>
      obtain ⟨fs, fG, fdefs, fΓ, fenv, fhΓ, fht, fbody⟩ := f
      cases kens with
      | none => exact hens.elim
      | some sk =>
        obtain ⟨sks, skΓ⟩ := sk
        cases ens with
        | none => simp at hensm
        | some es =>
          obtain ⟨eΓ, es⟩ := es
          obtain ⟨rfl, rfl, hve⟩ := hens
          simp only [Bool.and_eq_true, beq_iff_eq] at hensm
          obtain ⟨hes, hesΓ⟩ := hensm
          obtain rfl := eq_of_sames hesΓ
          obtain ⟨⟨⟩, hE⟩ := Fun.eq_siteFn hP _ es (hrE _ rfl) (hsE ⟨eΓ, es⟩ rfl) hes.symm
          refine ⟨Ty.up (.tuple _) (PendingShape.hdata _) (kv, rvalue, fenv, renv, ()),
            relDs_up _ _ _ _ ⟨_, _, rfl, hK, _, _, rfl, hvi, _, _, rfl, hve, _, _, rfl, hva, rfl⟩, ?_⟩
          simp only [PendingShape.pending]
          erw [Ty.down_up]
          dsimp only at hA hE
          rw [hA, hE]
          rfl

end

section
variable {e : Ty} {L : Layout}

theorem relAlts_pendingInj (d : Nat) : (shs : List (PendingShape e)) → (k j : Nat) → {sh : PendingShape e} →
    (h : shs[j]? = some sh) → (fx : Ty.dens sh.fields) → {vals : List Val} → RelVs L sh.fields fx vals →
    RelAlts L d k (shs.map PendingShape.fields) (pendingInj shs j h fx) (.ctor d (k + j) vals)
  | s :: _, k, 0, sh, h, fx, vals, hr => by
    obtain rfl : s = sh := Option.some.inj h
    exact ⟨vals, rfl, hr⟩
  | _ :: shs, k, j + 1, _, h, fx, vals, hr => by
    have := relAlts_pendingInj d shs (k + 1) j h fx hr
    simp only [pendingInj]
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact this

/-- The shape index of each request kind, for requests the sender `snd` starts: the shape that fits the kind and the
external that lists it. Own kinds have none: their effects never reach the pending table. -/
def shapeIdxs (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (snd : (ks : List Ty) × SenderShape ks)
    (keys : List EffectKey) : Except Refusal (List Nat) :=
  keys.mapM fun key => do
    let x ← need (.layout (.effectKind key.name)) (key.owner ds)
    need (.layout (.effectKind key.name)) (shs.findIdx? (·.fits snd key x))

/-- The pending entry of the effect kind `i`'s value `eff`, with the shape `j` and the sender's key tuple items
`keyT`. -/
def entryAt (dE dP dk : Nat) (keyT : List Term) (eff : Term) (i j : Nat) : Term :=
  .ctor dP j [.ctor dk 0 keyT, .sel dE i 0 eff, .sel dE i 1 eff, .sel dE i 2 eff]

/-- The pending entry of the effect `eff`: the entry of its kind, from the kinds' shape indices `js`. With no kind no
effect has a code, so no slot holding one is read; the entry is then `dflt`, any term of the entry's sort. -/
def entryT (dE dP dk : Nat) (dflt : Term) (keyT : List Term) (eff : Term) : Nat → List Nat → Term
  | _, [] => dflt
  | i, [j] => entryAt dE dP dk keyT eff i j
  | i, j :: js => .ite (.is dE i eff) (entryAt dE dP dk keyT eff i j) (entryT dE dP dk dflt keyT eff (i + 1) js)

theorem entryT_den {M : Model} (dE dP dk : Nat) (dflt : Term) (keyT : List Term) (eff : Term) {vals : List Val} :
    (js : List Nat) → (i0 i : Nat) → eff.denote M = .ctor dE (i0 + i) vals → (j : Nat) → js[i]? = some j →
    (entryT dE dP dk dflt keyT eff i0 js).denote M = (entryAt dE dP dk keyT eff (i0 + i) j).denote M
  | [], _, _, _, _, h => by cases h
  | [j'], i0, 0, _, j, h => by cases h; rfl
  | [_], _, _ + 1, _, _, h => by cases h
  | j' :: j'' :: js, i0, 0, he, j, h => by
    cases h
    simp [entryT, Term.denote, he, Val.toBool]
  | j' :: j'' :: js, i0, i + 1, he, j, h => by
    have ih := entryT_den dE dP dk dflt keyT eff (j'' :: js) (i0 + 1) i (by rw [he]; congr 1; omega) j (by simpa using h)
    have hne : (Term.is dE i0 eff).denote M = .bool false := by simp [Term.denote, he]
    rw [show i0 + (i + 1) = i0 + 1 + i by omega, ← ih]
    show (if (Term.denote M (.is dE i0 eff)).toBool then _ else _) = _
    rw [hne]
    rfl

/-- The pending entry the step writes for an effect a sender starts: wherever the effect's term and the key tuple's
items denote them, the entry term denotes an entry that codes the request with its sender and the external that lists
it. -/
theorem entry_rel {M : Model} {P : List AnySite} (hP : SitesUnique P) {e : Ty} {ks : List Ty} (sd : SenderShape ks)
    {shs : List (PendingShape e)} (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)} {js : List Nat}
    (hjs : shapeIdxs shs ds ⟨ks, sd⟩ (L.effectsOf e) = .ok js)
    {dE nE dP nP dk : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (kv : (Ty.tuple ks).den0) {keyT : List Term} (hK : RelD L (.tuple ks) kv (.ctor dk 0 (Term.denotes M keyT)))
    {eff : EffectV e} (hr : eff.Reach P) (hreq : eff.isRequest = true) {effT : Term}
    (heff : RelV L (.dsl .effect [e]) eff (effT.denote M)) (id : Nat) (dflt : Term) :
    ∃ req x, eff = .request req ∧ req.ownerIn ds = some x ∧ ∃ y,
      RelV L (pendingEntry shs) y ((entryT dE dP dk dflt keyT effT 0 js).denote M) ∧
      pendingOf shs id y = ⟨id, sd.sender kv, x, req⟩ := by
  obtain ⟨d, n, hd, ⟨i, key, vals, hki, hz, hh⟩ | ⟨i, key, vals, -, -, hh⟩⟩ := heff
  case inr =>
    cases eff with
    | request => cases key <;> exact hh.elim
    | command => cases hreq
    | query => cases hreq
  obtain rfl : dE = d := find_det hE hd
  cases eff with
  | command => exact hh.elim
  | query => exact hh.elim
  | request req =>
    obtain ⟨j, hj, hbody⟩ := forall2_getElem? (mapM_ok _ _ _ hjs) hki
    obtain ⟨x, hx, hbody⟩ := bind_ok.1 hbody
    have hfind := need_ok.1 hbody
    obtain ⟨hlt, hfit, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
    have hsh : shs[j]? = some shs[j] := List.getElem?_eq_getElem hlt
    obtain ⟨fx, hrel, hpend⟩ := fits_pending hP (hshs _ (List.getElem_mem hlt)) hfit hr hh kv hK id
    refine ⟨req, x, rfl, (owner_eq hh ds).trans (need_ok.1 hx), pendingInj shs j hsh fx, ?_, ?_⟩
    · obtain ⟨-, -, -, -, -, -, vi, ve, va, rfl, -⟩ := hh
      rw [entryT_den dE dP dk dflt keyT effT (vals := [vi, ve, va]) js 0 i (by rw [hz, Nat.zero_add]) j hj]
      have := relAlts_pendingInj (L := L) dP shs 0 j hsh fx hrel
      simp only [Nat.zero_add] at this
      refine ⟨dP, nP, hPE, ?_⟩
      simp only [entryAt, Term.denote, Term.denotes, hz]
      simpa using this
    · rw [pendingOf_inj id shs j hsh fx, hpend]

end

end Tazuna.Smt
