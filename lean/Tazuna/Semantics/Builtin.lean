import Tazuna.Ir.Builtin
import Tazuna.Semantics.Gleam
import Tazuna.Semantics.Value

/-! The meaning of each built-in. Bags are lists whose order no operation reveals (`Prim.den_rel` proves it, with
renamed fresh ids); tables are lists of pairs whose keys differ, which the type of a table demands. Every function here is generic over the values it holds, so the meaning of a built-in is the same at
every instance. -/

namespace Tazuna.Ir

namespace Builtin

/-- The one item whose key wins against every other: `none` reports an empty bag, `some none` a tie. -/
def pick {α : Type} (wins : Int → Int → Bool) (key : α → Int) : List α → Except Bool α
  | [] => .error false
  | x :: rest =>
    let best := rest.foldl (fun m y => if wins (key y) m then key y else m) (key x)
    match (x :: rest).filter (key · == best) with
    | [w] => .ok w
    | _ => .error true

def sumBy {α : Type} (f : α → Int) (xs : List α) : Int := (xs.map f).foldl (· + ·) 0

section Table
variable {k v : Sem}

/-- Whether `a` and `b` are the same key, asked both ways. -/
def sameKey (k : Sem) (a b : k.1) : Bool := k.2 a b || k.2 b a

def tableEmpty : (Sem.table k v).1 := ⟨[], .nil⟩

def tableRemove (key : k.1) (t : (Sem.table k v).1) : (Sem.table k v).1 :=
  ⟨t.1.filter (!sameKey k key ·.1), t.2.filter _⟩

/-- The table with `key` mapped to `value`: the old entry goes and the new one joins at the end. -/
def tableInsert (key : k.1) (value : v.1) (t : (Sem.table k v).1) : (Sem.table k v).1 :=
  ⟨(tableRemove key t).1 ++ [(key, value)], by
    refine List.pairwise_append.2 ⟨(tableRemove key t).2, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    simp only [tableRemove, List.mem_filter, sameKey, Bool.not_eq_true', Bool.or_eq_false_iff] at ha
    exact ⟨ha.2.2, ha.2.1⟩⟩

def tableFilter (keep : k.1 → v.1 → Bool) (t : (Sem.table k v).1) : (Sem.table k v).1 :=
  ⟨t.1.filter (fun e => keep e.1 e.2), t.2.filter _⟩

def tableMap {w : Sem} (f : k.1 → v.1 → w.1) (t : (Sem.table k v).1) : (Sem.table k w).1 :=
  ⟨t.1.map (fun e => (e.1, f e.1 e.2)), List.pairwise_map.2 (t.2.imp id)⟩

end Table

end Builtin

open Builtin

def Ty.ok {a e : Ty} (x : a.den) : (Ty.result a e).den := .inl (x, ())
def Ty.error {a e : Ty} (x : e.den) : (Ty.result a e).den := .inr (.inl (x, ()))
def Ty.some {a : Ty} (x : a.den) : (Ty.option a).den := .inl (x, ())
def Ty.none {a : Ty} : (Ty.option a).den := .inr (.inl ())

def Ty.ofPick {a : Ty} : Except Bool a.den → (Ty.result a .pickError).den
  | .ok x => Ty.ok x
  | .error false => Ty.error (e := .pickError) (.inl ())
  | .error true => Ty.error (e := .pickError) (.inr (.inl ()))

mutual
theorem Ty.isData_inst {args : List Ty} (h : ∀ t ∈ args, t.isData = true) :
    (t : Ty) → t.isData = true → (t.inst args).isData = true
  | .int, _ | .str, _ | .date, _ | .id, _ => rfl
  | .param k, _ => by
    simp only [Ty.inst]
    cases e : args[k]? with
    | none => rfl
    | some u => exact h u (List.mem_of_getElem? e)
  | .list t, ht | .bag t, ht => by simp only [Ty.isData] at ht ⊢; exact Ty.isData_inst h t ht
  | .tuple ts, ht => by simp only [Ty.isData] at ht ⊢; exact Ty.isDatas_inst h ts ht
  | .fn ps r, ht => by
    simp only [Ty.isData, Ty.inst, Bool.and_eq_true] at ht ⊢; exact ⟨Ty.isDatas_inst h ps ht.1, Ty.isData_inst h r ht.2⟩
  | .adt _ _ vs, ht => by simp only [Ty.isData] at ht ⊢; exact Ty.isDatass_inst h vs ht
  | .table k v, ht => by
    simp only [Ty.isData, Ty.inst, Bool.and_eq_true] at ht ⊢; exact ⟨Ty.isData_inst h k ht.1, Ty.isData_inst h v ht.2⟩
  | .dsl _ _, ht => by simpa [Ty.isData, Ty.inst] using ht
theorem Ty.isDatas_inst {args : List Ty} (h : ∀ t ∈ args, t.isData = true) :
    (ts : List Ty) → Ty.isDatas ts = true → Ty.isDatas (Ty.insts args ts) = true
  | [], _ => rfl
  | t :: ts, ht => by
    simp only [Ty.isDatas, Ty.insts, Bool.and_eq_true] at ht ⊢; exact ⟨Ty.isData_inst h t ht.1, Ty.isDatas_inst h ts ht.2⟩
theorem Ty.isDatass_inst {args : List Ty} (h : ∀ t ∈ args, t.isData = true) :
    (vs : List (List Ty)) → Ty.isDatass vs = true → Ty.isDatass (Ty.instss args vs) = true
  | [], _ => rfl
  | ts :: vs, ht => by
    simp only [Ty.isDatass, Ty.instss, Bool.and_eq_true] at ht ⊢
    exact ⟨Ty.isDatas_inst h ts ht.1, Ty.isDatass_inst h vs ht.2⟩
end

theorem Prim.dataOf {p : Prim} {args : List Ty} (h : p.ok args = true) (hp : p.sig.dataArgs = true) :
    ∀ t ∈ args, t.isData = true := by
  simp only [Prim.ok, hp, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

/-- A data argument of a structure built-in, as the structure value holds it. -/
abbrev Prim.dn {args : List Ty} (h : ∀ t ∈ args, t.isData = true) (t : Ty) (ht : t.isData = true := by rfl)
    (x : (t.inst args).den) : (t.inst args).den0 :=
  Ty.down _ (Ty.isData_inst h t ht) x

/-- A data value handed to a function of the spec. -/
abbrev Prim.up {args : List Ty} (h : ∀ t ∈ args, t.isData = true) (k : Nat) (x : ((Ty.param k).inst args).den0) :
    ((Ty.param k).inst args).den :=
  Ty.up _ (Ty.isData_inst h (.param k) rfl) x

def Ty.toOption {t : Ty} : (Ty.option t).den → Option t.den
  | .inl (x, ()) => Option.some x
  | .inr _ => Option.none

-- The built-in's arity (`Prim.ok`) guarantees the type argument, so that default is never read. A subscription
-- whose event no source declares has no owner, which the empty name says.
set_option linter.tazuna.silentDefault false in
/-- The value of a built-in at the type arguments `args`, which meet its demands. -/
def Prim.den : (p : Prim) → (args : List Ty) → p.ok args = true → (p.ty.inst args).den
  | .length, _, _ => fun (s, ()) => Gleam.length s.1
  | .bagFromList, _, _ => fun (xs, ()) => xs
  | .bagInsert, _, _ => fun (xs, x, ()) => x :: xs
  | .bagSize, _, _ => fun (xs, ()) => (xs.length : Int)
  | .bagFilter, _, _ => fun (xs, f, ()) => xs.filter fun x => Ty.toBool (f (x, ()))
  | .bagMap, _, _ => fun (xs, f, ()) => xs.map fun x => f (x, ())
  | .bagCount, _, _ => fun (xs, f, ()) => ((xs.filter fun x => Ty.toBool (f (x, ()))).length : Int)
  | .bagSum, _, _ => fun (xs, f, ()) => sumBy (fun x => f (x, ())) xs
  | .bagAny, _, _ => fun (xs, f, ()) => Ty.ofBool (xs.any fun x => Ty.toBool (f (x, ())))
  | .bagAll, _, _ => fun (xs, f, ()) => Ty.ofBool (xs.all fun x => Ty.toBool (f (x, ())))
  | .bagContains, args, _ => fun (xs, x, ()) => Ty.ofBool (xs.any (Ty.deq (args[0]?.getD (.param 0)) x))
  | .bagMinBy, _, _ => fun (xs, f, ()) => Ty.ofPick (pick (· < ·) (fun x => f (x, ())) xs)
  | .bagMaxBy, _, _ => fun (xs, f, ()) => Ty.ofPick (pick (· > ·) (fun x => f (x, ())) xs)
  | .tableNew, _, _ => fun () => Builtin.tableEmpty
  | .tableFromList, _, _ => fun (pairs, ()) => pairs.foldl (fun t (k, v, ()) => Builtin.tableInsert k v t) tableEmpty
  | .tableInsert, _, _ => fun (t, k, v, ()) => Builtin.tableInsert k v t
  | .tableRemove, _, _ => fun (t, k, ()) => Builtin.tableRemove k t
  | .tableGet, args, _ => fun (t, k, ()) => match lookupBy (Ty.deq (args[0]?.getD (.param 0))) k t.1 with
    | .some v => Ty.some v
    | .none => Ty.none
  | .tableSize, _, _ => fun (t, ()) => (t.1.length : Int)
  | .tableKeys, _, _ => fun (t, ()) => t.1.map (·.1)
  | .tableValues, _, _ => fun (t, ()) => t.1.map (·.2)
  | .tableFilter, _, _ => fun (t, f, ()) => Builtin.tableFilter (fun k v => Ty.toBool (f (k, v, ()))) t
  | .tableMap, _, _ => fun (t, f, ()) => Builtin.tableMap (fun k v => f (k, v, ())) t
  | .tableCount, _, _ => fun (t, f, ()) => ((t.1.filter fun (k, v) => Ty.toBool (f (k, v, ()))).length : Int)
  | .tableAny, _, _ => fun (t, f, ()) => Ty.ofBool (t.1.any fun (k, v) => Ty.toBool (f (k, v, ())))
  | .tableAll, _, _ => fun (t, f, ()) => Ty.ofBool (t.1.all fun (k, v) => Ty.toBool (f (k, v, ())))
  | .dateAddDays, _, _ => fun (d, n, ()) => @HAdd.hAdd Int Int Int _ d n
  | .dateDaysBetween, _, _ => fun (a, b, ()) => @HSub.hSub Int Int Int _ b a
  | .require, _, _ => fun (holds, rejection, next, ()) => if Ty.toBool holds then next () else Ty.error rejection
  | .spec, _, _ => fun (services, externals, ()) =>
    let services : List ServiceV := services
    let externals : List ExternalV := externals
    let declared := externals.flatMap fun x => x.declares.map (x.name, ·)
    let sources := services.flatMap (fun v => v.sources.map fun (n, t) => (v.name, n, t)) ++
      externals.flatMap fun x => x.declares.filterMap fun | .source n t => some (x.name, n, t) | _ => none
    let ownerOf (name : String) (t : Ty) : String :=
      ((sources.find? fun (_, n, u) => n == name && (Ty.same t u).isSome).map (·.1)).getD ""
    ⟨services.map fun v => { v with declared, subscribes := v.subscribes.map fun sub =>
      { sub with source := ownerOf sub.name sub.event } }, externals⟩
  | .service, args, h => let d := Prim.dataOf h rfl
    fun (name, init, apply, subscribes, declares, machines, reactions, invariants, responses, bnds, scenarios, ()) =>
    let R := (Ty.param 0).inst args
    let E := (Ty.param 1).inst args
    let C := (Ty.param 2).inst args
    let declares : List DeclaredV := declares
    { name := name.1, records := R, event := E, caller := C,
      init := Prim.dn d (.param 0) rfl init, apply,
      subscribes, machines, reactions,
      declares,
      commands := declares.filterMap fun
        | .command r e c x => match Ty.same r R, Ty.same e E, Ty.same c C with
          | some ⟨h1⟩, some ⟨h2⟩, some ⟨h3⟩ => some (h1 ▸ h2 ▸ h3 ▸ x)
          | _, _, _ => none
        | _ => none,
      queries := declares.filterMap fun
        | .query r c x => match Ty.same r R, Ty.same c C with
          | some ⟨h1⟩, some ⟨h2⟩ => some (h1 ▸ h2 ▸ x)
          | _, _ => none
        | _ => none,
      sources := declares.filterMap fun | .source n t => some (n, t) | _ => none,
      invariants, responses, bounds := bnds, scenarios,
      declared := [] }
  | .command, args, h => let d := Prim.dataOf h rfl
    fun (name, callers, accepts, decide, ensures, ()) =>
    Subtype.mk (p := fun (x : CommandV _ _ _) => x.input = (Ty.param 3).inst args ∧ x.rejection = (Ty.param 4).inst args)
    { name := name.1, input := (Ty.param 3).inst args, rejection := (Ty.param 4).inst args,
      callers := Prim.dn d (.list (.origin (.param 2))) rfl callers,
      accepts, decide, ensures } ⟨rfl, rfl⟩
  | .query, args, h => let d := Prim.dataOf h rfl
    fun (name, callers, accepts, resolve, ()) =>
    Subtype.mk (p := fun (x : QueryV _ _) => x.input = (Ty.param 2).inst args ∧ x.output = (Ty.param 3).inst args)
    { name := name.1, input := (Ty.param 2).inst args, output := (Ty.param 3).inst args,
      callers := Prim.dn d (.list (.origin (.param 1))) rfl callers,
      accepts, resolve } ⟨rfl, rfl⟩
  | .declareCommand, args, _ => fun (x, ()) =>
    .command ((Ty.param 0).inst args) ((Ty.param 1).inst args) ((Ty.param 2).inst args) x.1
  | .declareQuery, args, _ => fun (x, ()) => .query ((Ty.param 0).inst args) ((Ty.param 2).inst args) x.1
  | .declareSource, args, _ => fun (name, ()) => .source name ((Ty.param 3).inst args)
  | .declareExternalCommand, args, _ => fun (name, ()) =>
    .externalCommand name ((Ty.param 0).inst args) ((Ty.param 1).inst args) ((Ty.param 2).inst args)
  | .declareExternalQuery, args, _ => fun ((name, holds), ()) =>
    .externalQuery name ((Ty.param 0).inst args) ((Ty.param 1).inst args) holds
  | .machine, args, h => let d := Prim.dataOf h rfl
    fun (name, instances, initial, on, timer, effect, invariants, ()) =>
    { name := name.1, key := (Ty.param 2).inst args, state := (Ty.param 3).inst args,
      instances, initial := Prim.dn d (.param 3) rfl initial, on, timer,
      effect, invariants }
  | .reaction, _, _ => fun (name, react, ()) => { name := name.1, react }
  | .external, _, _ => fun (name, declares, ()) => ⟨name.1, declares⟩
  | .externalCommand, _, _ => fun (name, ()) => name.1
  | .externalQuery, _, _ => fun (name, ensures, ()) => (name.1, ensures)
  | .source, _, _ => fun (name, ()) => name.1
  | .requestCommand, args, h => let d := Prim.dataOf h rfl
    fun (name, input, onAnswer, ()) => .request
    { name, input := (Ty.param 1).inst args, output := (Ty.param 2).inst args,
      rejection := some ((Ty.param 3).inst args), value := Prim.dn d (.param 1) rfl input, ensures := none,
      onAnswer }
  | .requestQuery, args, h => let d := Prim.dataOf h rfl
    fun ((name, ensures), input, onAnswer, ()) =>
    .request
    { name, input := (Ty.param 1).inst args, output := (Ty.param 2).inst args, rejection := none,
      value := Prim.dn d (.param 1) rfl input, ensures := some ensures, onAnswer }
  | .sendCommand, args, h => let d := Prim.dataOf h rfl
    fun (c, input, onAnswer, ()) =>
    let c : CommandOf ((Ty.param 0).inst args) ((Ty.param 1).inst args) ((Ty.param 2).inst args)
      ((Ty.param 3).inst args) ((Ty.param 4).inst args) := c
    .command c.1.name ((Ty.param 2).inst args) _ _ (Prim.dn d (.param 3) rfl input) onAnswer
  | .sendQuery, args, h => let d := Prim.dataOf h rfl
    fun (q, input, onAnswer, ()) =>
    let q : QueryOf ((Ty.param 0).inst args) ((Ty.param 2).inst args) ((Ty.param 3).inst args)
      ((Ty.param 4).inst args) := q
    .query q.1.name ((Ty.param 2).inst args) _ _ (Prim.dn d (.param 3) rfl input) onAnswer
  | .subscribe, args, _ => fun (name, wrap, ()) =>
    { source := "", name, event := (Ty.param 1).inst args, wrap }
  | .bounds, _, _ => fun (creates, items, cascade, steps, ()) => { creates, items, cascade, steps }
  | .create, args, _ => fun (table, atMost, ()) =>
    { key := (Ty.param 1).inst args, value := (Ty.param 2).inst args, table, atMost }
  | .response, _, _ => fun (name, after, then_, within, ()) => { name := name.1, after, then_, within }
  | .scenario, _, _ => fun (name, steps, ()) => { name := name.1, steps }
  | .stepCommand, args, h => let d := Prim.dataOf h rfl
    fun (c, caller, input, ()) =>
    let c : CommandOf ((Ty.param 0).inst args) ((Ty.param 1).inst args) ((Ty.param 2).inst args)
      ((Ty.param 3).inst args) ((Ty.param 4).inst args) := c
    .command c.1 (Prim.dn d (.param 2) rfl caller) (cast (congrArg Ty.den0 c.2.1.symm) (Prim.dn d (.param 3) rfl input))
      fun _ => []
  | .stepCommandThen, args, h => let d := Prim.dataOf h rfl
    fun (c, caller, input, next, ()) =>
    let c : CommandOf ((Ty.param 0).inst args) ((Ty.param 1).inst args) ((Ty.param 2).inst args)
      ((Ty.param 3).inst args) ((Ty.param 4).inst args) := c
    .command c.1 (Prim.dn d (.param 2) rfl caller) (cast (congrArg Ty.den0 c.2.1.symm) (Prim.dn d (.param 3) rfl input))
      fun n => next (n, ())
  | .stepQuery, args, h => let d := Prim.dataOf h rfl
    fun (q, caller, input, ()) =>
    let q : QueryOf ((Ty.param 0).inst args) ((Ty.param 2).inst args) ((Ty.param 3).inst args)
      ((Ty.param 4).inst args) := q
    .query q.1 (Prim.dn d (.param 2) rfl caller) (cast (congrArg Ty.den0 q.2.1.symm) (Prim.dn d (.param 3) rfl input))
  | .stepWait, _, _ => fun (ms, ()) => .wait ms
  | .stepAnswerCommand, args, h => let d := Prim.dataOf h rfl
    fun (name, sender, value, ()) =>
    .answer name ((Ty.param 3).inst args) ((Ty.param 4).inst args) (some ((Ty.param 5).inst args)) sender
      ⟨_, Prim.dn d (.result (.param 4) (.param 5)) rfl value⟩
  | .stepAnswerQuery, args, h => let d := Prim.dataOf h rfl
    fun ((name, _), sender, value, ()) =>
    .answer name ((Ty.param 3).inst args) ((Ty.param 4).inst args) none sender ⟨_, Prim.dn d (.param 4) rfl value⟩
  | .stepEvent, args, h => let d := Prim.dataOf h rfl
    fun (name, value, ()) => .event name ⟨(Ty.param 3).inst args, Prim.dn d (.param 3) rfl value⟩
  | .fromMachine, args, h => let d := Prim.dataOf h rfl
    fun (m, key, ()) =>
    let m : MachineV ((Ty.param 0).inst args) ((Ty.param 1).inst args) := m
    .machine m.name ⟨(Ty.param 2).inst args, Prim.dn d (.param 2) rfl key⟩
  | .fromReaction, args, _ => fun (x, ()) =>
    let x : ReactionV ((Ty.param 0).inst args) ((Ty.param 1).inst args) := x
    .reaction x.name
  | .fresh, _, _ => fun (step, index, ()) => IdV.fresh step index
  | .tableLookup, args, _ => fun (t, k, rejection, next, ()) => match lookupBy (Ty.deq (args[0]?.getD (.param 0))) k t.1 with
    | .some v => next (v, ())
    | .none => Ty.error rejection

/-! Examples, one or more per built-in: what each means at a concrete instance. -/

section Examples
open Ty (ofBool toBool)

private def I (x : Int) : Int := x
private def pos (x : Int) : Ty.bool.den := ofBool (decide (0 < x))
private def isOk {a e : Ty} : (Ty.result a e).den → Option a.den
  | .inl (x, ()) => .some x
  | .inr _ => .none
private def pickFailure {a : Ty} : (Ty.result a .pickError).den → Option Bool
  | .inr (.inl (.inl (), ())) => .some false
  | .inr (.inl (.inr _, ())) => .some true
  | .inl _ => .none
private def table : (Ty.table .int .str).den := ⟨[((1 : Int), (str! "a")), ((2 : Int), (str! "bb"))], by simp [KeysUnique, Ty.semWith]⟩

example : Prim.length.den [] rfl (str! "e\u0301", ()) = (2 : Int) := rfl
example : Prim.bagFromList.den [.int] rfl (([1, 1, 2] : List Int), ()) = ([1, 1, 2] : List Int) := rfl
example : Prim.bagInsert.den [.int] rfl (([1] : List Int), (1 : Int), ()) = ([1, 1] : List Int) := rfl
example : Prim.bagSize.den [.int] rfl (([1, 1, 2] : List Int), ()) = (3 : Int) := rfl
example : Prim.bagFilter.den [.int] rfl (([-1, 2, 3] : List Int), fun (x, ()) => pos x, ()) = ([2, 3] : List Int) := rfl
example : Prim.bagMap.den [.int, .int] rfl (([1, 2] : List Int), fun (x, ()) => I x * 10, ()) = ([10, 20] : List Int) := rfl
example : Prim.bagCount.den [.int] rfl (([-1, 2, 3] : List Int), fun (x, ()) => pos x, ()) = (2 : Int) := rfl
example : Prim.bagSum.den [.int] rfl (([1, 2, 3] : List Int), fun (x, ()) => I x * 10, ()) = (60 : Int) := rfl
example : toBool (Prim.bagAny.den [.int] rfl (([-1, 2] : List Int), fun (x, ()) => pos x, ())) = true := rfl
example : toBool (Prim.bagAll.den [.int] rfl (([-1, 2] : List Int), fun (x, ()) => pos x, ())) = false := rfl
example : toBool (Prim.bagContains.den [.int] rfl (([1, 2] : List Int), (2 : Int), ())) = true := rfl
-- One least key picks its item; an empty bag is Empty and a shared least key is Tie, whatever the order.
example : isOk (Prim.bagMinBy.den [.str] rfl (([(str! "bb"), (str! "a")] : List Str), fun (s, ()) => (s.1.length : Int), ())) = .some (str! "a") := rfl
example : pickFailure (Prim.bagMinBy.den [.str] rfl (([] : List Str), fun (s, ()) => (s.1.length : Int), ())) = .some false := rfl
example : pickFailure (Prim.bagMinBy.den [.str] rfl (([(str! "a"), (str! "b")] : List Str), fun (s, ()) => (s.1.length : Int), ())) = .some true := rfl
example : isOk (Prim.bagMaxBy.den [.str] rfl (([(str! "bb"), (str! "a")] : List Str), fun (s, ()) => (s.1.length : Int), ())) = .some (str! "bb") := rfl
example : (Prim.tableNew.den [.int, .str] rfl ()).1 = ([] : List (Int × Str)) := rfl
-- A later pair replaces an earlier one's value.
example : (Prim.tableFromList.den [.int, .str] rfl (([((1 : Int), (str! "a"), ()), ((1 : Int), (str! "b"), ())] : List (Int × Str × Unit)), ())).1 = ([(1, (str! "b"))] : List (Int × Str)) := rfl
example : (Prim.tableInsert.den [.int, .str] rfl (table, (1 : Int), (str! "c"), ())).1 = ([(2, (str! "bb")), (1, (str! "c"))] : List (Int × Str)) := rfl
example : (Prim.tableInsert.den [.int, .str] rfl (table, (3 : Int), (str! "c"), ())).1 = ([(1, (str! "a")), (2, (str! "bb")), (3, (str! "c"))] : List (Int × Str)) := rfl
example : (Prim.tableRemove.den [.int, .str] rfl (table, (1 : Int), ())).1 = ([(2, (str! "bb"))] : List (Int × Str)) := rfl
example : Prim.tableGet.den [.int, .str] rfl (table, (2 : Int), ()) = Ty.some (a := .str) (str! "bb") := rfl
example : Prim.tableGet.den [.int, .str] rfl (table, (3 : Int), ()) = Ty.none (a := .str) := rfl
example : Prim.tableSize.den [.int, .str] rfl (table, ()) = (2 : Int) := rfl
example : Prim.tableKeys.den [.int, .str] rfl (table, ()) = ([1, 2] : List Int) := rfl
example : Prim.tableValues.den [.int, .str] rfl (table, ()) = [(str! "a"), (str! "bb")] := rfl
example : (Prim.tableFilter.den [.int, .str] rfl (table, fun (k, _, ()) => pos (I k - 1), ())).1 = ([(2, (str! "bb"))] : List (Int × Str)) := rfl
example : (Prim.tableMap.den [.int, .str, .int] rfl (table, fun (_, v, ()) => (v.1.length : Int), ())).1 =
  ([(1, 1), (2, 2)] : List (Int × Int)) := rfl
example : Prim.tableCount.den [.int, .str] rfl (table, fun (k, _, ()) => pos k, ()) = (2 : Int) := rfl
example : toBool (Prim.tableAny.den [.int, .str] rfl (table, fun (k, _, ()) => pos (I k - 1), ())) = true := rfl
example : toBool (Prim.tableAll.den [.int, .str] rfl (table, fun (k, _, ()) => pos (I k - 1), ())) = false := rfl
example : Prim.dateAddDays.den [] rfl ((100 : Int), (-3 : Int), ()) = (97 : Int) := rfl
example : Prim.dateDaysBetween.den [] rfl ((100 : Int), (97 : Int), ()) = (-3 : Int) := rfl
-- `use <- require(holds, r)` continues when it holds and rejects with r otherwise.
example : isOk (Prim.require.den [.int, .str] rfl (ofBool true, (str! "r"), fun () => Ty.ok (e := .str) (1 : Int), ()))
  = .some (1 : Int) := rfl
example : Prim.require.den [.int, .str] rfl (ofBool false, (str! "r"), fun () => Ty.ok (e := .str) (1 : Int), ()) =
  Ty.error (a := .int) (e := .str) (str! "r") := rfl
-- `use v <- ref(table, key, r)` continues with the key's value and rejects with r when the key is absent.
example : isOk (Prim.tableLookup.den [.int, .str, .str, .str] rfl (table, (2 : Int), (str! "r"), fun (v, ()) => Ty.ok (e := .str) v, ()))
  = .some (str! "bb") := rfl
example : Prim.tableLookup.den [.int, .str, .str, .str] rfl (table, (3 : Int), (str! "r"), fun (v, ()) => Ty.ok (e := .str) v, ()) =
  Ty.error (a := .str) (e := .str) (str! "r") := rfl

end Examples

end Tazuna.Ir
