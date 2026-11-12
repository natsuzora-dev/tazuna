import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Matching

open Tazuna.Data Tazuna.Verify

mutual

/--
Whether snapshot value `s` matches implementation value `t`, where `rename` gives the implementation value of a snapshot
createKey value. A string matches itself or the implementation value of its key. Arrays and runs match element by
element, objects with the same keys match field by field, and bags match in some order.
-/
def ValueMatches (rename : String → Option String) : CValue → CValue → Prop
  | .leaf v, t =>
    match v with
    | .str s => ∃ w, t = .leaf (.str w) ∧ (w = s ∨ rename s = some w)
    | _ => t = .leaf v
  | .arr xs, t => ∃ ys, t = .arr ys ∧ ListMatches rename xs ys
  | .runs xs, t => ∃ ys, t = .runs ys ∧ ListMatches rename xs ys
  | .bag xs, t => ∃ ys zs, t = .bag ys ∧ ys.Perm zs ∧ ListMatches rename xs zs
  | .obj fs, t =>
    ∃ gs, t = .obj gs ∧ (∀ k, k ∈ fs.map (·.1) ↔ k ∈ gs.map (·.1)) ∧ FieldsMatch rename fs gs

def ListMatches (rename : String → Option String) : List CValue → List CValue → Prop
  | [], [] => True
  | x :: xs, y :: ys => ValueMatches rename x y ∧ ListMatches rename xs ys
  | _, _ => False

def FieldsMatch (rename : String → Option String) : List (String × CValue) → List (String × CValue) → Prop
  | [], _ => True
  | (k, v) :: fs, gs => (∃ w, gs.lookup k = some w ∧ ValueMatches rename v w) ∧ FieldsMatch rename fs gs

end

/-- Two missing values match, and one missing value matches nothing. -/
def ContentMatches (rename : String → Option String) : Option CValue → Option CValue → Prop
  | some s, some t => ValueMatches rename s t
  | none, none => True
  | _, _ => False

/-- The context that verify compares `snapshot` in. -/
def context (snapshot : List (Option Line)) (internal : Line → Bool) : Ctx :=
  { requests := (snapshot.filterMap fun l => l.bind fun l => l.body.id.map (·, l)).reverse,
    follows := mustFollow snapshot,
    internal }

/-- The `out` lines of a window that verify pairs: neither subscribe nor unsubscribe lines, nor internal events. -/
def pairedOut (internal : Line → Bool) (w : Window) : List Out :=
  w.before.filter fun o => !o.line.isSubscribing && !internal o.line

/-- The subscriptions open after window `k`. -/
def openAfter (ws : List Window) (k : Nat) : List (String × Subscription) :=
  (ws.take (k + 1)).foldl (fun o w => follow o (w.before.filter (·.line.isSubscribing))) []

/--
Whether implementation subscription `t` was paired, after window `k` or an earlier window, with an open snapshot
subscription that has the type, name and value of the open snapshot subscription `s`, as `Q` pairs them.
-/
def Subscribed (ws : List Window) (Q : Nat → List (String × String)) (k : Nat) (s t : String) : Prop :=
  ∃ j ≤ k, ∃ o a b, (o, t) ∈ Q j ∧ (openAfter ws j).lookup s = some a ∧ (openAfter ws j).lookup o = some b ∧
    alike a.out.line b.out.line = true

/-- Whether the implementation names `t` where the snapshot names `s`: by the renamed id, or a like subscription. -/
def Placed (ids : String → Option String) (subscribed : String → String → Prop) :
    Option String → Option String → Prop
  | some s, some t => ids s = some t ∨ subscribed s t
  | none, none => True
  | _, _ => False

/-- A snapshot `out` line `s` and the implementation `out` line `t` paired with it. -/
structure OutMatches (keys ids : String → Option String) (subscribed : String → String → Prop) (c : Ctx)
    (s t : Line) : Prop where
  type : t.body.type = s.body.type
  time : t.time.time = s.time.time
  place : match s.body with
    | .answer _ _ to _ => Placed ids subscribed (some to) t.body.to?
    | _ => t.body.name? = s.body.name?
  content : ContentMatches keys (c.compared s t).1 (c.compared s t).2

/-- A snapshot `in` line `s` and the implementation `in` line `t` at the same position. -/
structure InMatches (keys ids : String → Option String) (subscribed : String → String → Prop) (s t : Line) :
    Prop where
  type : t.body.type = s.body.type
  name : t.body.name? = s.body.name?
  time : t.time.time = s.time.time
  id : ∀ i j, s.body.id = some i → t.body.id = some j → ids i = some j
  rest : match s.body with
    | .time .. | .restart .. => True
    | .unsubscribe _ _ to => Placed ids subscribed (some to) t.body.to?
    | .answer _ _ to _ => Placed ids subscribed (some to) t.body.to? ∧ ContentMatches keys s.content t.content
    | _ => Placed ids subscribed s.body.resultOf? t.body.resultOf? ∧ ContentMatches keys s.content t.content

/-- A pairing `Q` of the open snapshot subscriptions `os` with the open implementation subscriptions `ot`. -/
def OpenMatches (keys : String → Option String) (os ot : List (String × Subscription))
    (Q : List (String × String)) : Prop :=
  (Q.map (·.1)).Perm (os.map (·.1)) ∧ (Q.map (·.2)).Perm (ot.map (·.1)) ∧
    ∀ q ∈ Q, ∃ s t, os.lookup q.1 = some s ∧ ot.lookup q.2 = some t ∧ s.name = t.name ∧
      ContentMatches keys s.out.line.content t.out.line.content

/--
The implementation trace `lines` matches `snapshot`, up to what verify ignores. `keys` renames the snapshot's
createKey values and `ids` its ids, each to distinct implementation values; a subscription may instead be named by one
that `Q` paired with an alike subscription. In each window `P k` pairs the compared `out` lines one to one in the
snapshot's `after` order, and `Q k` pairs the subscriptions open after the window. The `in` lines at the same position
match. An `out` request's id is only checked through the lines that name it, and alike requests may swap.
-/
def Matches (snapshot lines : List (Option Line)) (internal : Line → Bool) : Prop :=
  let E := steps snapshot
  let A := steps lines
  let c := context snapshot internal
  E.length = A.length ∧
    ∃ (keys ids : String → Option String) (P : Nat → List (Out × Out)) (Q : Nat → List (String × String)),
      (∀ a b x, keys a = some x → keys b = some x → a = b) ∧
      (∀ a x, keys a = some x → ∃ l, some l ∈ snapshot ∧ a ∈ l.created.getD []) ∧
      (∀ a b x, ids a = some x → ids b = some x → a = b) ∧
      ∀ k (e a : Window), E[k]? = some e → A[k]? = some a →
        ((P k).map (·.1)).Perm (pairedOut internal e) ∧ ((P k).map (·.2)).Perm (pairedOut internal a) ∧
        (∀ p ∈ P k, OutMatches keys ids (Subscribed E Q k) c p.1.line p.2.line) ∧
        (∀ p ∈ P k, ∀ q ∈ P k, p.1.index - 1 ∈ mustFollow snapshot (q.1.index - 1) → p.2.index < q.2.index) ∧
        OpenMatches keys (openAfter E k) (openAfter A k) (Q k) ∧
        e.input.isSome = a.input.isSome ∧
        ∀ s t, e.input = some s → a.input = some t → InMatches keys ids (Subscribed E Q k) s.line t.line

end Tazuna.Thm.Verify.Matching
