import Tazuna.Ir.Surface
import Tazuna.Ir.Ty

/-! Everything the `tazuna` Gleam module declares: its types, its aliases and its built-in functions. This table is the
one source: elaboration reads the signatures, `Tazuna.Semantics.Builtin` gives each function its meaning, and
`lake exe gen-dsl` writes the Gleam declarations, whose bodies only panic. The set stays general: no calendars, time
zones or formats. -/

namespace Tazuna.Ir

/-- A type `tazuna` declares without variants: Lean gives it a meaning of its own. -/
structure OpaqueType where
  /-- The module of the `tazuna` package that declares it. -/
  module : String
  name : String
  params : List String
  doc : String
  make : List Ty → Option Ty

def opaqueTypes : List OpaqueType :=
  [ ⟨"tazuna/bag", "Bag", ["a"], "A multiset: two bags are equal when each value occurs as often in both. Where tazuna puts values in an order the spec does not write, it uses Erlang term order, the order Gleam's Erlang target compares values in; a bag compares as the list of its items in ascending order.",
      fun | [t] => some (.bag t) | _ => none⟩,
    ⟨"tazuna/table", "Table", ["k", "v"], "A finite map from keys to values; at most one value per key. A table in the records, a machine state, a type that crosses the wire or what a kept function captures has a plain key: Int, String, Date, Id, or a custom type or tuple of these.",
      fun | [k, v] => some (.table k v) | _ => none⟩,
    ⟨"tazuna/date", "Date", [], "A day. Dates have no calendar: a spec adds days and counts the days between two dates.",
      fun | [] => some .date | _ => none⟩,
    ⟨"tazuna", "Id", [], "An identifier a step makes fresh, or one from outside the service; ids compare with `==` only.",
      fun | [] => some .id | _ => none⟩ ] ++
  (Dsl.all.filter (!·.kept)).map fun k => ⟨"tazuna", k.name, k.decl.2.1, k.decl.2.2,
    fun args => if args.length == k.decl.2.1.length then some (.dsl k args) else none⟩

/-- The type a global name such as `tazuna/bag.Bag` names at `args`, when a `tazuna` module declares it opaque. -/
def opaqueTy? (name : String) (args : List Ty) : Option Ty :=
  (opaqueTypes.find? (fun t => t.module ++ "." ++ t.name == name)).bind (·.make args)

/-- Aliases `tazuna` declares, with their documentation. -/
def builtinAliases : List (Surface.AliasDef × String) :=
  [ (⟨"tazuna.Instant", [], .con "Int" [], ⟨0, 0⟩⟩, "A point in time, in milliseconds."),
    (⟨"tazuna.Duration", [], .con "Int" [], ⟨0, 0⟩⟩, "A length of time, in milliseconds."),
    (⟨"tazuna.Rules", [], .con "List" [.tuple [.con "String" [], .con "Bool" []]], ⟨0, 0⟩⟩,
      "Named rules, as `invariants`, `accepts` and `ensures` return them: each holds or not.") ]

/-- The Ints the DSL writes as a time alias, so a signature says which Int is a time: (the declaring type or built-in,
the field or parameter label, the alias). -/
def timeAliases : List (String × String × String) :=
  [ ("tazuna.Ctx", "now", "Instant"), ("tazuna.MachineCtx", "now", "Instant"), ("tazuna.ReactionCtx", "now", "Instant"),
    ("tazuna.QueryCtx", "now", "Instant"),
    ("tazuna.Timer", "after", "Duration"), ("response", "within", "Duration"), ("step_wait", "for", "Duration") ]

/-- The built-in functions. -/
inductive Prim where
  | length
  | bagFromList | bagInsert | bagSize | bagFilter | bagMap | bagCount | bagSum | bagAny | bagAll | bagContains
  | bagMinBy | bagMaxBy
  | tableNew | tableFromList | tableInsert | tableRemove | tableGet | tableSize | tableKeys | tableValues
  | tableFilter | tableMap | tableCount | tableAny | tableAll
  | dateAddDays | dateDaysBetween
  | require | tableLookup
  | spec | service | command | query | machine | reaction
  | external | externalCommand | externalQuery | source
  | declareCommand | declareQuery | declareSource | declareExternalCommand | declareExternalQuery
  | requestCommand | requestQuery | sendCommand | sendQuery | subscribe | bounds | create | response
  | scenario | stepCommand | stepQuery | stepWait | stepAnswerCommand | stepAnswerQuery | stepEvent | fromMachine | fromReaction | fresh | stepCommandThen
deriving Repr, DecidableEq

structure PrimParam where
  label : Option String
  name : String
  ty : Ty

structure PrimSig where
  name : String
  doc : String
  tvars : List String
  params : List PrimParam
  ret : Ty
  /-- The type variables `==` must work on (`Ty.comparable`), by index. -/
  needsEq : List Nat := []
  /-- Whether every type variable must be data (`Ty.isData`): a structure value holds data of those types. -/
  dataArgs : Bool := false

namespace Prim

open Ty in
def sig : Prim → PrimSig :=
  let a := param 0
  let b := param 1
  let k := param 0
  let v := param 1
  let p (n : String) (t : Ty) : PrimParam := ⟨none, n, t⟩
  let l (lab : String) (t : Ty) : PrimParam := ⟨some lab, lab, t⟩
  -- A function the structure value keeps, closed over the data it captures.
  let kept (t : Ty) : Ty := .dsl .closure [t]
  -- A kept function that takes data and returns effects.
  let keptEffects (t : Ty) : Ty := .dsl .effectClosure [t]
  fun
  | .length => ⟨"length", "The number of code points.", [], [p "string" .str], .int, [], false⟩
  | .bagFromList => ⟨"from_list", "A bag of the list's items.", ["a"], [p "items" (.list a)], .bag a, [], false⟩
  | .bagInsert => ⟨"insert", "The bag with one more occurrence of the item.", ["a"],
      [p "bag" (.bag a), p "item" a], .bag a, [], false⟩
  | .bagSize => ⟨"size", "The number of items, counting each occurrence.", ["a"], [p "bag" (.bag a)], .int, [], false⟩
  | .bagFilter => ⟨"filter", "The items that satisfy the predicate.", ["a"],
      [p "bag" (.bag a), l "keeping" (.fn [a] .bool)], .bag a, [], false⟩
  | .bagMap => ⟨"map", "Each item transformed, occurrences kept.", ["a", "b"],
      [p "bag" (.bag a), l "with" (.fn [a] b)], .bag b, [], false⟩
  | .bagCount => ⟨"count", "The number of items that satisfy the predicate.", ["a"],
      [p "bag" (.bag a), l "where" (.fn [a] .bool)], .int, [], false⟩
  | .bagSum => ⟨"sum", "The sum of the function over the items.", ["a"],
      [p "bag" (.bag a), l "of" (.fn [a] .int)], .int, [], false⟩
  | .bagAny => ⟨"any", "Whether some item satisfies the predicate.", ["a"],
      [p "bag" (.bag a), l "satisfying" (.fn [a] .bool)], .bool, [], false⟩
  | .bagAll => ⟨"all", "Whether every item satisfies the predicate.", ["a"],
      [p "bag" (.bag a), l "satisfying" (.fn [a] .bool)], .bool, [], false⟩
  | .bagContains => ⟨"contains", "Whether the item occurs in the bag.", ["a"],
      [p "bag" (.bag a), p "item" a], .bool, [0], false⟩
  | .bagMinBy => ⟨"min_by", "The one item with the least key; Empty or Tie when there is not exactly one.",
      ["a"], [p "bag" (.bag a), l "by" (.fn [a] .int)], .result a .pickError, [], false⟩
  | .bagMaxBy => ⟨"max_by", "The one item with the greatest key; Empty or Tie when there is not exactly one.",
      ["a"], [p "bag" (.bag a), l "by" (.fn [a] .int)], .result a .pickError, [], false⟩
  | .tableNew => ⟨"new", "The table without keys.", ["k", "v"], [], .table k v, [0], false⟩
  | .tableFromList => ⟨"from_list", "A table of the pairs; a later pair replaces an earlier one's value.",
      ["k", "v"], [p "pairs" (.list (.tuple [k, v]))], .table k v, [0], false⟩
  | .tableInsert => ⟨"insert", "The table with the key mapped to the value, replacing any value it had.",
      ["k", "v"], [p "table" (.table k v), p "key" k, p "value" v], .table k v, [0], false⟩
  | .tableRemove => ⟨"remove", "The table without the key.", ["k", "v"],
      [p "table" (.table k v), p "key" k], .table k v, [0], false⟩
  | .tableGet => ⟨"get", "The key's value, if the table has the key.", ["k", "v"],
      [p "table" (.table k v), p "key" k], .option v, [0], false⟩
  | .tableSize => ⟨"size", "The number of keys.", ["k", "v"], [p "table" (.table k v)], .int, [], false⟩
  | .tableKeys => ⟨"keys", "The keys.", ["k", "v"], [p "table" (.table k v)], .bag k, [], false⟩
  | .tableValues => ⟨"values", "The values, one occurrence per key.", ["k", "v"],
      [p "table" (.table k v)], .bag v, [], false⟩
  | .tableFilter => ⟨"filter", "The entries that satisfy the predicate.", ["k", "v"],
      [p "table" (.table k v), l "keeping" (.fn [k, v] .bool)], .table k v, [], false⟩
  | .tableMap => ⟨"map", "Each value transformed, keys kept.", ["k", "v", "w"],
      [p "table" (.table k v), l "with" (.fn [k, v] (param 2))], .table k (param 2), [], false⟩
  | .tableCount => ⟨"count", "The number of entries that satisfy the predicate.", ["k", "v"],
      [p "table" (.table k v), l "where" (.fn [k, v] .bool)], .int, [], false⟩
  | .tableAny => ⟨"any", "Whether some entry satisfies the predicate.", ["k", "v"],
      [p "table" (.table k v), l "satisfying" (.fn [k, v] .bool)], .bool, [], false⟩
  | .tableAll => ⟨"all", "Whether every entry satisfies the predicate.", ["k", "v"],
      [p "table" (.table k v), l "satisfying" (.fn [k, v] .bool)], .bool, [], false⟩
  | .dateAddDays => ⟨"add_days", "The date that many days later (earlier when negative).", [],
      [p "date" .date, p "days" .int], .date, [], false⟩
  | .dateDaysBetween => ⟨"days_between", "The days from the first date to the second: negative when it is earlier.",
      [], [l "from" .date, l "to" .date], .int, [], false⟩
  | .require => ⟨"require",
      "`use <- tazuna.require(holds, or: rejection)`: the rest of the block when it holds, else the rejection.",
      ["a", "e"], [p "holds" .bool, ⟨some "or", "rejection", param 1⟩, l "then" (.fn [] (.result a (param 1)))],
      .result a (param 1), [], false⟩
  | .tableLookup => ⟨"lookup",
      "`use value <- table.lookup(table, key, or: rejection)`: the rest of the block with the key's value, else the rejection.",
      ["k", "v", "a", "e"],
      [p "table" (.table k v), p "key" k, ⟨some "or", "rejection", param 3⟩, l "then" (.fn [v] (.result (param 2) (param 3)))],
      .result (param 2) (param 3), [0], false⟩
  | .spec =>
    { name := "spec", doc := "The spec: its services and the externals they talk to.",
      tvars := [],
      params := [l "services" (.list (.dsl .service [])), l "externals" (.list (.dsl .external []))],
      ret := .dsl .spec [] }
  | .service =>
    { name := "service",
      doc := "A service. `apply` folds an event into the records: events are the only writes. The service owns the commands, queries and sources it declares, and its scenarios run from `init` at time 0.",
      tvars := ["records", "event", "caller"], dataArgs := true, needsEq := [2],
      params := [l "name" .str, l "init" a, l "apply" (kept (.fn [a, b] a)),
        l "subscribes" (.list (.dsl .subscription [b])), l "declares" (.list (.dsl .declared [a, b, param 2])),
        l "machines" (.list (.dsl .machine [a, b])),
        l "reactions" (.list (.dsl .reaction [a, b])), l "invariants" (kept (.fn [a] Ty.rules)),
        l "responses" (.list (.dsl .response [b])), l "bounds" (.dsl .bounds [a]),
        l "scenarios" (.list (.dsl .scenario [a, b, param 2]))],
      ret := .dsl .service [] }
  | .command =>
    { name := "command",
      doc := "A command, named by a string literal: callers outside `callers` or input breaking `accepts` make it Invalid; `decide` accepts with events or rejects. The service that lists it owns it.",
      tvars := ["records", "event", "caller", "input", "rejection"], dataArgs := true, needsEq := [2],
      params := [l "name" .str, l "callers" (.list (param 2)), l "accepts" (kept (.fn [param 3] Ty.rules)),
        l "decide" (kept (.fn [.ctx a (param 3) (param 2)] (.result (.list b) (param 4)))),
        l "ensures" (kept (.fn [.ctx a (param 3) (param 2), a] Ty.rules))],
      ret := .dsl .command [a, b, param 2, param 3, param 4] }
  | .query =>
    { name := "query", doc := "A query, named by a string literal: it answers from the records, writes nothing and makes no ids, so `resolve` sees no source of fresh ids. The service that lists it owns it.",
      tvars := ["records", "caller", "input", "output"], dataArgs := true, needsEq := [1],
      params := [l "name" .str, l "callers" (.list b), l "accepts" (kept (.fn [param 2] Ty.rules)),
        l "resolve" (kept (.fn [.queryCtx a (param 2) b] (param 3)))],
      ret := .dsl .query [a, b, param 2, param 3] }
  | .machine =>
    { name := "machine",
      doc := "A machine: one instance per key in `instances`, starting at `initial`; `on` reacts to each event, a due timer enters its state on a clock line, and entering a state may start an effect. A machine's instances react, start and fire in Erlang term order of their keys, so the key type is Int, String, Date, Id, Bool, an enumeration, or a tuple or one-variant record of these.",
      tvars := ["records", "event", "key", "state"], dataArgs := true, needsEq := [2],
      params := [l "name" .str, l "instances" (kept (.fn [a] (.bag (param 2)))), l "initial" (param 3),
        l "on" (kept (.fn [.machineCtx (param 2) (param 3) a, b] (.next (param 3)))),
        l "after" (kept (.fn [.machineCtx (param 2) (param 3) a] (.option (.timer (param 3))))),
        l "effect" (keptEffects (.fn [.machineCtx (param 2) (param 3) a] (.option (.dsl .effect [b])))),
        l "invariants" (kept (.fn [.machineCtx (param 2) (param 3) a] Ty.rules))],
      ret := .dsl .machine [a, b] }
  | .reaction =>
    { name := "reaction", doc := "A reaction: effects for each event, without state of its own.",
      tvars := ["records", "event"], dataArgs := true,
      params := [l "name" .str, l "react" (keptEffects (.fn [.reactionCtx a, b] (.list (.dsl .effect [b]))))],
      ret := .dsl .reaction [a, b] }
  | .external =>
    { name := "external", doc := "An external service: the commands, queries and sources it declares, which it owns.", tvars := [],
      params := [l "name" .str, l "declares" (.list (.dsl .declared [Ty.nil, Ty.nil, Ty.nil]))],
      ret := .dsl .external [] }
  | .externalCommand =>
    { name := "external_command", doc := "A command of an external, named by a string literal. The external that lists it owns it; check requires one to.",
      tvars := ["input", "output", "rejection"], dataArgs := true,
      params := [l "name" .str], ret := .dsl .externalCommand [a, b, param 2] }
  | .externalQuery =>
    { name := "external_query",
      doc := "A query of an external, named by a string literal; `ensures` says what its answers satisfy. The external that lists it owns it; check requires one to.",
      tvars := ["input", "output"], dataArgs := true,
      params := [l "name" .str, l "ensures" (kept (.fn [a, b] Ty.rules))],
      ret := .dsl .externalQuery [a, b] }
  | .source =>
    { name := "source", doc := "Events named `name`: the service or external that lists the source sends them.",
      tvars := ["event"], dataArgs := true,
      params := [l "name" .str], ret := .dsl .source [a] }
  | .declareCommand =>
    { name := "declare_command", doc := "The command, for the declarations of the service that owns it.",
      tvars := ["records", "event", "caller", "input", "rejection"], dataArgs := true,
      params := [p "command" (.dsl .command [a, b, param 2, param 3, param 4])],
      ret := .dsl .declared [a, b, param 2] }
  | .declareQuery =>
    { name := "declare_query", doc := "The query, for the declarations of the service that owns it.",
      tvars := ["records", "event", "caller", "input", "output"], dataArgs := true,
      params := [p "query" (.dsl .query [a, param 2, param 3, param 4])],
      ret := .dsl .declared [a, b, param 2] }
  | .declareSource =>
    { name := "declare_source", doc := "The source, for the declarations of the service or external that owns it.",
      tvars := ["records", "event", "caller", "source"], dataArgs := true,
      params := [p "source" (.dsl .source [param 3])],
      ret := .dsl .declared [a, b, param 2] }
  | .declareExternalCommand =>
    { name := "declare_external_command", doc := "The command, for the declarations of the external that owns it.",
      tvars := ["input", "output", "rejection"], dataArgs := true,
      params := [p "command" (.dsl .externalCommand [a, b, param 2])],
      ret := .dsl .declared [Ty.nil, Ty.nil, Ty.nil] }
  | .declareExternalQuery =>
    { name := "declare_external_query", doc := "The query, for the declarations of the external that owns it.",
      tvars := ["input", "output"], dataArgs := true,
      params := [p "query" (.dsl .externalQuery [a, b])],
      ret := .dsl .declared [Ty.nil, Ty.nil, Ty.nil] }
  | .requestCommand =>
    { name := "request_command",
      doc := "An effect: the request to an external's command, and the events its answer becomes.",
      tvars := ["event", "input", "output", "rejection"], dataArgs := true,
      params := [l "command" (.dsl .externalCommand [b, param 2, param 3]), l "input" b,
        l "on_answer" (kept (.fn [.result (param 2) (param 3)] (.list a)))],
      ret := .dsl .effect [a] }
  | .requestQuery =>
    { name := "request_query",
      doc := "An effect: the request to an external's query, and the events its answer becomes. An answer that breaks the query's `ensures` is Invalid.",
      tvars := ["event", "input", "output"], dataArgs := true,
      params := [l "query" (.dsl .externalQuery [b, param 2]), l "input" b,
        l "on_answer" (kept (.fn [param 2] (.list a)))],
      ret := .dsl .effect [a] }
  | .sendCommand =>
    { name := "send_command",
      doc := "An effect: the service runs its own command within the same step; `on_answer` gets Ok(Nil) once the command's events are applied, or its rejection.",
      tvars := ["records", "event", "caller", "input", "rejection"], dataArgs := true,
      params := [l "command" (.dsl .command [a, b, param 2, param 3, param 4]), l "caller" (param 2),
        l "input" (param 3), l "on_answer" (kept (.fn [.result Ty.nil (param 4)] (.list b)))],
      ret := .dsl .effect [b] }
  | .sendQuery =>
    { name := "send_query", doc := "An effect: the service runs its own query within the same step.",
      tvars := ["records", "event", "caller", "input", "output"], dataArgs := true,
      params := [l "query" (.dsl .query [a, param 2, param 3, param 4]), l "caller" (param 2),
        l "input" (param 3), l "on_answer" (kept (.fn [param 4] (.list b)))],
      ret := .dsl .effect [b] }
  | .subscribe =>
    { name := "subscribe", doc := "Receives the events of another service's or an external's source as this service's events.",
      tvars := ["event", "source"], dataArgs := true,
      params := [l "to" (.dsl .source [b]), l "wrap" (kept (.fn [b] a))], ret := .dsl .subscription [a] }
  | .bounds =>
    { name := "bounds",
      doc := "How far checking goes: records per table (`creates`), items per bag and per table no create bounds, internal steps per input, steps per run.",
      tvars := ["records"], dataArgs := true,
      params := [l "creates" (.list (.dsl .create [a])), l "items" .int, l "cascade" .int, l "steps" .int],
      ret := .dsl .bounds [a] }
  | .create =>
    { name := "create",
      doc := "At most this many records in the table that `table` reads, a table field of the records, at any time.",
      tvars := ["records", "k", "v"], dataArgs := true,
      params := [l "table" (kept (.fn [a] (.table b (param 2)))), l "at_most" .int], ret := .dsl .create [a] }
  | .response =>
    { name := "response", doc := "After an event satisfying `after`, one satisfying `then` within the duration `within`.",
      tvars := ["event"], dataArgs := true,
      params := [l "name" .str, l "after" (.fn [a] .bool), l "then" (.fn [a] .bool), l "within" .int],
      ret := .dsl .response [a] }
  | .scenario =>
    { name := "scenario",
      doc := "A scenario of the service that lists it: its steps run from the initial records at time 0, and `test` compares the trace with snapshots/<service>/<name>.jsonl.",
      tvars := ["records", "event", "caller"], dataArgs := true,
      params := [l "name" .str, l "steps" (.list (.dsl .step [a, b, param 2]))],
      ret := .dsl .scenario [a, b, param 2] }
  | .stepCommand =>
    { name := "step_command", doc := "A step: the caller sends the command.",
      tvars := ["records", "event", "caller", "input", "rejection"], dataArgs := true,
      params := [l "command" (.dsl .command [a, b, param 2, param 3, param 4]), l "caller" (param 2),
        l "input" (param 3)],
      ret := .dsl .step [a, b, param 2] }
  | .stepQuery =>
    { name := "step_query", doc := "A step: the caller sends the query.",
      tvars := ["records", "event", "caller", "input", "output"], dataArgs := true,
      params := [l "query" (.dsl .query [a, param 2, param 3, param 4]), l "caller" (param 2), l "input" (param 3)],
      ret := .dsl .step [a, b, param 2] }
  | .stepWait =>
    { name := "step_wait", doc := "A step: time moves on by the duration, and the timers due fire.",
      tvars := ["records", "event", "caller"], dataArgs := true,
      params := [⟨some "for", "duration", .int⟩], ret := .dsl .step [a, b, param 2] }
  | .stepAnswerCommand =>
    { name := "step_answer_command",
      doc := "A step: the external answers the one pending request to `command` that `sender` sent.",
      tvars := ["records", "event", "caller", "input", "output", "rejection"], dataArgs := true,
      params := [l "command" (.dsl .externalCommand [param 3, param 4, param 5]), l "sender" (.dsl .sender []),
        l "with" (.result (param 4) (param 5))],
      ret := .dsl .step [a, b, param 2] }
  | .stepAnswerQuery =>
    { name := "step_answer_query",
      doc := "A step: the external answers the one pending request to `query` that `sender` sent.",
      tvars := ["records", "event", "caller", "input", "output"], dataArgs := true,
      params := [l "query" (.dsl .externalQuery [param 3, param 4]), l "sender" (.dsl .sender []),
        l "with" (param 4)],
      ret := .dsl .step [a, b, param 2] }
  | .stepEvent =>
    { name := "step_event", doc := "A step: the service receives an event of a source it subscribes to.",
      tvars := ["records", "event", "caller", "source"], dataArgs := true,
      params := [l "source" (.dsl .source [param 3]), l "value" (param 3)],
      ret := .dsl .step [a, b, param 2] }
  | .fromMachine =>
    { name := "from_machine", doc := "The instance of the machine whose key is `key`, as the sender of a request.",
      tvars := ["records", "event", "key"], dataArgs := true,
      params := [l "machine" (.dsl .machine [a, b]), l "key" (param 2)], ret := .dsl .sender [] }
  | .fromReaction =>
    { name := "from_reaction", doc := "The reaction, as the sender of a request.",
      tvars := ["records", "event"], dataArgs := true,
      params := [l "reaction" (.dsl .reaction [a, b])], ret := .dsl .sender [] }
  | .fresh =>
    { name := "fresh", doc := "The `index`-th new id of this step: ids from different steps or indices differ.",
      tvars := [], params := [p "source" (.dsl .fresh []), p "index" .int], ret := .id }
  | .stepCommandThen =>
    { name := "step_command_then",
      doc := "A step: the caller sends the command, and `then` gives the steps after it. `then` receives the source of the command's new ids, so `fresh(source, index)` is the id the command made with `fresh(ctx.fresh, index)`; written with `use`, the source is a variable gleam checks.",
      tvars := ["records", "event", "caller", "input", "rejection"], dataArgs := true,
      params := [l "command" (.dsl .command [a, b, param 2, param 3, param 4]), l "caller" (param 2),
        l "input" (param 3), l "then" (.fn [.dsl .fresh []] (.list (.dsl .step [a, b, param 2])))],
      ret := .dsl .step [a, b, param 2] }

def all : List Prim :=
  [.length, .bagFromList, .bagInsert, .bagSize, .bagFilter, .bagMap, .bagCount, .bagSum, .bagAny, .bagAll,
   .bagContains, .bagMinBy, .bagMaxBy, .tableNew, .tableFromList, .tableInsert, .tableRemove, .tableGet, .tableSize,
   .tableKeys, .tableValues, .tableFilter, .tableMap, .tableCount, .tableAny, .tableAll, .dateAddDays,
   .dateDaysBetween, .require, .tableLookup, .spec, .service, .command, .query, .machine, .reaction,
   .external, .externalCommand, .externalQuery, .source, .declareCommand, .declareQuery, .declareSource,
   .declareExternalCommand, .declareExternalQuery, .requestCommand, .requestQuery,
   .sendCommand, .sendQuery, .subscribe, .bounds, .create, .response, .scenario, .stepCommand, .stepQuery, .stepWait,
   .stepAnswerCommand, .stepAnswerQuery, .stepEvent, .fromMachine, .fromReaction, .fresh, .stepCommandThen]

theorem mem_all (p : Prim) : p ∈ all := by cases p <;> simp [all]

/-- The generic type, with `param k` for the `k`-th type variable. -/
def ty (p : Prim) : Ty := .fn (p.sig.params.map (·.ty)) p.sig.ret

def labels (p : Prim) : List (Option String) := p.sig.params.map (·.label)

-- A missing type argument is not comparable, so the check fails.
set_option linter.tazuna.silentDefault false in
/-- Whether the type arguments meet the signature's demands. -/
def ok (p : Prim) (args : List Ty) : Bool :=
  args.length == p.sig.tvars.length && p.sig.needsEq.all (fun k => (args[k]?.map Ty.comparable).getD false) &&
    (!p.sig.dataArgs || args.all Ty.isData)

/-- The module of the `tazuna` package that declares the built-in: data built-ins sit beside their type, as
`gleam/dict` holds `Dict`'s functions. -/
def module : Prim → String
  | .bagFromList | .bagInsert | .bagSize | .bagFilter | .bagMap | .bagCount | .bagSum | .bagAny | .bagAll
  | .bagContains | .bagMinBy | .bagMaxBy => "tazuna/bag"
  | .tableNew | .tableFromList | .tableInsert | .tableRemove | .tableGet | .tableSize | .tableKeys | .tableValues
  | .tableFilter | .tableMap | .tableCount | .tableAny | .tableAll | .tableLookup => "tazuna/table"
  | .dateAddDays | .dateDaysBetween => "tazuna/date"
  | _ => "tazuna"

/-- The global name, such as `tazuna/bag.filter`. -/
def global (p : Prim) : String := p.module ++ "." ++ p.sig.name

/-- The built-in a global name refers to. -/
def byName? (name : String) : Option Prim := all.find? (·.global == name)

end Prim

end Tazuna.Ir
