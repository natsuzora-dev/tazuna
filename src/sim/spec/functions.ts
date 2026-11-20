import type { z } from "zod";
import { type Bag, bagValues, NotOnly } from "../../data/bag.ts";
import { comparableAnswer, comparable as comparableOf, orderFree } from "../../data/canonical.ts";
import { bag, bagged, decoded, defaultRow, encoded, toJson } from "../../data/collections.ts";
import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { Ensured } from "../../data/ensured.generated.ts";
import { expectFound, InternalError } from "../../data/internalError.ts";
import { partAt, type SchemaStep } from "../../data/jsonSchema.ts";
import type { Activity } from "../../data/step.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import type { TransitionRef } from "../../data/transitionRef.generated.ts";
import { type Fields, type Json, objectOf, type Shape, strictObjectOf } from "../../data/values.ts";
import { thrown, zodError } from "../../data/violation.ts";
import { stateAt, transitionAt } from "../../dsl/chart.ts";
import { type Conditions, firstFailing } from "../../dsl/conditions.ts";
import type {
  AnyCommand,
  AnyControl,
  AnyEvent,
  AnyQuery,
  Automation,
  Binds,
  ChartSpec,
  Emit as DefinedEmit,
  Definition,
  Named,
  ServiceDefinition,
  StateSpec,
  TransitionSpec,
} from "../../dsl/definition.ts";
import { type AnyEntity, type AnyKeyedEntity, type Ref, refTarget } from "../../dsl/entity.ts";
import type { Spec } from "../../load/load.ts";
import { type Schema, type Service, serviceOf } from "../../service/basic.ts";
import {
  type Access,
  type Assignment,
  type Checked,
  type Decided,
  type Edge,
  Failed,
  type Functions,
  givenKeys,
  type Holder,
  type Keys,
  lists,
  type Scope,
} from "../../service/functions.ts";
import { chartOf, mapOf } from "../../service/instance.ts";
import type { Emit } from "../../service/message.ts";
import type { RecordSource } from "../../service/records.ts";
import { type ChartStructure, chartStructure, stateNamed } from "../../spec/structure.ts";
import { isDescendant } from "../../spec/tree.ts";
import { ensured } from "./contract.ts";
import { recordsView } from "./records.ts";

// Every `input` and `payload` argument here is a decoded value.

/**
 * Runs author code and returns its value. A throw becomes a `thrown` Issue, of `schema` when the code is that schema's
 * refinement or codec; the Issue of a held read inside passes through, `only()` on more than one value is notOnly, and
 * an InternalError stops the run.
 */
function attempt<T>(f: () => T, schema?: Schema): T | Failed {
  try {
    return f();
  } catch (error) {
    if (error instanceof InternalError) throw error;
    if (error instanceof Failed) return error;
    if (error instanceof NotOnly) return new Failed({ kind: "notOnly" });
    return new Failed(schema === undefined ? { kind: "thrown" } : { kind: "thrown", schema }, thrown(error));
  }
}

/**
 * Returns a value that author code made, encoded by `zod` in the order it was built, or the Issue of a value that does
 * not match `schema`.
 */
function encodedAnswer(schema: Schema, zod: z.ZodType, value: unknown): Json | Failed {
  const checked = attempt(() => encoded(zod, value), schema);
  if (checked instanceof Failed) return checked;
  return "error" in checked ? new Failed({ kind: "schema", schema }, zodError(checked.error.issues)) : checked.encoded;
}

const nonNull = (value: unknown): boolean => value !== null && value !== undefined;

/** Returns the function `name` of `functions`, which Lean names from the structure, so that it always exists. */
function named<F>(functions: Readonly<Record<string, F>> | undefined, name: string, what: string): F {
  const f = functions?.[name];
  if (f === undefined) throw new InternalError(`the definition has no ${what} ${name}`);
  return f;
}

/** Returns `target` with each property that an expression reads told to `read`. */
function readTracked<T extends object>(target: T, read: (property: string) => void): T {
  return new Proxy(target, {
    get: (t, p, receiver) => {
      if (typeof p === "string" && Object.hasOwn(t, p)) read(p);
      return Reflect.get(t, p, receiver);
    },
    has: (t, p) => {
      if (typeof p === "string") read(p);
      return Reflect.has(t, p);
    },
    ownKeys: (t) => {
      for (const p of Object.keys(t)) read(p);
      return Reflect.ownKeys(t);
    },
  });
}

/** Returns `args` with the properties of `extra`, defined by descriptor so that getters stay lazy until read. */
function extended<T extends object>(args: T, extra: object): T {
  return Object.defineProperties(
    {},
    { ...Object.getOwnPropertyDescriptors(args), ...Object.getOwnPropertyDescriptors(extra) },
  ) as T;
}

/** Returns a property that is made when an expression first reads it. */
function lazy(make: () => unknown): PropertyDescriptor {
  let made: { readonly value: unknown } | undefined;
  return {
    enumerable: true,
    get: () => {
      made ??= { value: make() };
      return made.value;
    },
  };
}

/**
 * Returns `held` of an expression whose state has the parameters `values`. Reading a name tells `read`; reading a name
 * that the state does not have throws an unheld Issue.
 */
function heldOf(values: Fields, read: () => void): object {
  return new Proxy(values, {
    get: (target, name) => {
      if (typeof name !== "string") return undefined;
      if (!Object.hasOwn(target, name)) throw new Failed({ kind: "unheld", held: name });
      read();
      return target[name];
    },
  });
}

type Assignments = Readonly<Record<string, (args: unknown) => unknown>>;

/** A machine or screen with its structure, and the nodes of its states as they are looked up. */
interface ChartOf {
  readonly named: Named<ChartSpec>;
  readonly ref: DefinitionRef;
  readonly structure: ChartStructure;
  readonly nodes: Map<string, StateSpec>;
}

/**
 * The definitions of the spec by kind, service and name, the charts of a service, and the view of the service that
 * semantics reads.
 */
interface Index {
  readonly definitions: ReadonlyMap<Definition["kind"], ReadonlyMap<string, ReadonlyMap<string, Named<Definition>>>>;
  readonly charts: Map<string, ChartOf>;
  readonly st: Service;
}

const indexes = new WeakMap<Spec, Map<string, Index>>();

function indexOf(spec: Spec, service: string): Index {
  const byService = indexes.get(spec) ?? new Map<string, Index>();
  indexes.set(spec, byService);
  const known = byService.get(service);
  if (known !== undefined) return known;
  const definitions = new Map<Definition["kind"], Map<string, Map<string, Named<Definition>>>>();
  for (const named of spec.definitions) {
    const byService = definitions.get(named.definition.kind) ?? new Map<string, Map<string, Named<Definition>>>();
    definitions.set(named.definition.kind, byService);
    const byName = byService.get(named.service) ?? new Map<string, Named<Definition>>();
    byService.set(named.service, byName);
    byName.set(named.name, named);
  }
  const index = { definitions, charts: new Map<string, ChartOf>(), st: serviceOf(spec.structure, service) };
  byService.set(service, index);
  return index;
}

/** The spec functions of `service`, which answer Lean's questions. */
export class SpecFunctions implements Functions {
  readonly st: Service;
  private readonly spec: Spec;
  private readonly service: string;
  private readonly owner: ServiceDefinition | undefined;
  private readonly index: Index;

  constructor(spec: Spec, service: string) {
    this.spec = spec;
    this.service = service;
    this.owner = spec.services.get(service)?.definition;
    this.index = indexOf(spec, service);
    this.st = this.index.st;
  }

  /** Returns the definition of one of `kinds` that `r` names. */
  definition<D>(kinds: readonly Definition["kind"][], r: DefinitionRef): Named<D> {
    for (const kind of kinds) {
      const found = this.index.definitions.get(kind)?.get(r.service)?.get(r.name);
      if (found !== undefined) return found as Named<D>;
    }
    throw new InternalError(`the spec has no ${kinds.join(" or ")} ${r.name} of ${r.service}`);
  }

  /** Returns the own definition of one of `kinds` named `name`. */
  private own<D>(kinds: readonly Definition["kind"][], name: string): Named<D> {
    return this.definition(kinds, { service: this.service, name });
  }

  /** Returns the shape of the values that `schema` checks: an input, output, payload, control payload, or context. */
  shape(schema: Schema): Shape {
    switch (schema.kind) {
      case "input":
      case "output": {
        const found = this.definition<{ readonly input?: Shape; readonly output?: Shape }>(
          ["command", "query", "screen"],
          schema.definition,
        ).definition;
        if (schema.kind === "input") return found.input ?? {};
        if (found.output === undefined) throw new InternalError(`${schema.definition.name} has no output`);
        return found.output;
      }
      case "payload":
        return this.definition<AnyEvent>(["event"], schema.event).definition.payload;
      case "control":
        return (
          this.control(this.definition<ChartSpec>(["screen"], schema.screen).definition, schema.control).payload ?? {}
        );
      case "record":
        return this.definition<AnyEntity>(["entity"], schema.entity).definition.fields as Shape;
      case "context":
        return this.chartOf(schema.chart.name).named.definition.context;
      case "mapContext":
        return this.mapNode(schema.chart.name, schema.map).context ?? {};
      case "mapKey":
        return this.mapNode(schema.chart.name, schema.map).key;
      case "held": {
        const held = this.node(schema.chart.name, schema.state).held;
        if (held === undefined) throw new InternalError(`the state ${schema.state} has no parameters`);
        return held as Shape;
      }
    }
  }

  private command(name: string): AnyCommand {
    return this.own<AnyCommand>(["command"], name).definition;
  }

  private query(name: string): Named<AnyQuery> {
    return this.own<AnyQuery>(["query"], name);
  }

  /** Returns the own machine or screen named `name`. */
  chartOf(name: string): ChartOf {
    const known = this.index.charts.get(name);
    if (known !== undefined) return known;
    const named = this.own<ChartSpec>(["machine", "screen"], name);
    const structure = chartStructure(this.spec.structure, named.service, named.name);
    if (structure === undefined) throw new InternalError(`the spec has no structure of the chart ${name}`);
    const chart = { named, ref: { service: named.service, name: named.name }, structure, nodes: new Map() };
    this.index.charts.set(name, chart);
    return chart;
  }

  /** Returns the state `state` of the machine or screen `machine`, which every question names from the structure. */
  node(machine: string, state: string): StateSpec {
    const { named, structure, nodes } = this.chartOf(machine);
    const known = nodes.get(state);
    if (known !== undefined) return known;
    const found = stateNamed(structure, state);
    if (found === undefined) throw new InternalError(`the chart ${machine} has no state ${state}`);
    const node = stateAt(named.definition, found.path);
    nodes.set(state, node);
    return node;
  }

  /** Returns the map state `map` of the machine or screen `machine`, which Lean names only as a map state. */
  private mapNode(machine: string, map: string): Extract<StateSpec, { readonly type: "map" }> {
    const node = this.node(machine, map);
    if (node.type !== "map") throw new InternalError(`the state ${map} of ${machine} is no map state`);
    return node;
  }

  /** Returns the control `control` of `chart`, which Lean names from the structure. */
  private control(chart: ChartSpec, control: string): AnyControl {
    return named(chart.controls, control, "control");
  }

  /** Returns the state that declares the expressions of a question that Lean always asks about a state. */
  private stateOf(scope: Scope): string {
    if (scope.state === null) throw new InternalError(`a question about ${chartOf(scope.id)} names no state`);
    return scope.state;
  }

  private transition(machine: string, t: TransitionRef): TransitionSpec {
    const { named, structure } = this.chartOf(machine);
    return transitionAt(named.definition, structure, t);
  }

  private assignments(machine: string, assignment: Assignment): Assignments | undefined {
    switch (assignment.kind) {
      case "transition":
        return this.transition(machine, assignment.transition).assign as Assignments | undefined;
      case "entry":
        return this.node(machine, assignment.state).entry?.assign as Assignments | undefined;
      case "exit":
        return this.node(machine, assignment.state).exit?.assign as Assignments | undefined;
    }
  }

  private entity(name: string): AnyEntity {
    const found = this.ownerDefinition().entities[name];
    if (found === undefined) throw new InternalError(`the service ${this.service} has no entity ${name}`);
    return found as AnyEntity;
  }

  /** Returns the service definition, which every question that reads records or entities has. */
  private ownerDefinition(): ServiceDefinition {
    if (this.owner === undefined) throw new InternalError(`the spec has no service ${this.service}`);
    return this.owner;
  }

  private view(records: RecordSource): Record<string, unknown> {
    return recordsView(this.ownerDefinition().entities, records);
  }

  /** Returns createKey over `keys`, what it returns next, and the entities that it was called for, in call order. */
  private keysFrom(keys: Keys): {
    readonly createKey: (key: Ref<AnyKeyedEntity>) => string;
    readonly created: readonly string[];
  } {
    const created: string[] = [];
    const createKey = (key: Ref<AnyKeyedEntity>) => {
      const entity = this.spec.names.get(refTarget(key));
      // Only a value of type `any` gets anything but ref() of an entity of the spec past the types.
      if (entity === undefined) throw new TypeError("createKey takes ref() of an entity of the spec");
      created.push(entity.name);
      return expectFound(`created key of ${entity.name}`, givenKeys(keys, created).at(-1))[1];
    };
    return { createKey, created };
  }

  /**
   * Returns the arguments that every expression of a Scope receives. Building active or records copies every state or
   * record, so they are built only when an expression reads them.
   */
  private baseArgs(scope: Scope, records: RecordSource, access: Access): Fields {
    const { structure } = this.chartOf(chartOf(scope.id));
    const copy = scope.copy;
    const context = copy === undefined ? scope.context : { ...scope.context, ...copy.context };
    const holder = (field: string): Holder =>
      copy !== undefined && Object.hasOwn(copy.context, field) ? "copy" : "owner";
    const map = mapOf(scope.id);
    const inCopy = (state: string) => map !== undefined && state !== map && isDescendant(structure, state, map);
    return Object.defineProperties(
      {
        context: readTracked(context, (field) => access.context(holder(field), field)),
        input: scope.input,
        shown: readTracked(Object.fromEntries(scope.shown), (slot) => access.shown(slot)),
        ...(copy === undefined ? {} : { key: copy.key }),
      },
      {
        records: lazy(() => this.view(records)),
        active: lazy(() => {
          const active = scope.active;
          return readTracked(Object.fromEntries(structure.states.map((s) => [s.name, active.has(s.name)])), (n) =>
            access.active(inCopy(n) ? "copy" : "owner", n),
          );
        }),
        now: {
          enumerable: true,
          get: () => {
            access.now();
            return scope.now;
          },
        },
      },
    );
  }

  /**
   * Returns the arguments of the expressions written in `scope.state`: the base arguments, `held` and `extra`. Reading
   * `held` reads the state's visit, which only entering the state writes.
   */
  private args(scope: Scope, records: RecordSource, access: Access, extra: Fields = {}): Fields {
    const base = this.baseArgs(scope, records, access);
    const { state } = scope;
    const read = () => {
      if (state !== null) access.active(scope.copy === undefined ? "owner" : "copy", state);
    };
    return extended(base, { held: heldOf(scope.held, read), ...extra });
  }

  /** Returns the input that `f` gives `target`, of the input shape `shape`, encoded as the sender writes it. */
  private writtenInput(
    target: DefinitionRef,
    shape: Shape,
    f: ((args: never) => unknown) | undefined,
    args: () => Fields,
  ): Json | Failed {
    const given = attempt(() => (f === undefined ? {} : f(args() as never)));
    return given instanceof Failed
      ? given
      : encodedAnswer({ kind: "input", definition: target }, strictObjectOf(shape), given);
  }

  /** Returns the binds values, which Lean asks for only once every binding is non-null. */
  private bound(binds: Binds<never>, args: Fields): Fields | Failed {
    return attempt(() =>
      Object.fromEntries(Object.entries(binds as Binds<Fields>).map(([name, f]) => [name, f(args)])),
    );
  }

  /** Returns whether the binds value `binding` is non-null. */
  private nonNullBinding(binds: Binds<never>, binding: string, args: Fields): boolean | Failed {
    const f = named(binds as Binds<Fields>, binding, "binding");
    const value = attempt(() => f(args));
    return value instanceof Failed ? value : nonNull(value);
  }

  /** Returns whether `condition` holds once every binds value is non-null, with the values as `bound`. */
  private boundHolds(
    binds: Binds<never>,
    conditions: Conditions<never>,
    condition: string,
    args: Fields,
  ): boolean | Failed {
    const values = this.bound(binds, args);
    if (values instanceof Failed) return values;
    const f = named(conditions as Conditions<Fields>, condition, "condition");
    return attempt(() => Boolean(f({ ...args, bound: values })));
  }

  parse(schema: Schema, value: unknown): Checked | Failed {
    const object = strictObjectOf(this.shape(schema));
    const parsed = attempt(() => object.safeParse(value), schema);
    if (parsed instanceof Failed) return parsed;
    if (!parsed.success) return { error: zodError(parsed.error.issues) };
    return { value: bagged(object, parsed.data) as Fields, encoded: toJson(object, parsed.data) };
  }

  fits(schema: Schema, path: readonly SchemaStep[], value: Json): boolean | Failed {
    const part = partAt(objectOf(this.shape(schema)), path);
    const parsed = attempt(() => part.safeParse(value), schema);
    return parsed instanceof Failed ? parsed : parsed.success;
  }

  /** Returns a decoded value of `schema` as JSON holds it, as Lean holds it (ChoiceDependent's Encode). */
  encode(schema: Schema, value: unknown): Json {
    const json = encoded(objectOf(this.shape(schema)), value);
    if ("error" in json) throw new InternalError(`a value of ${schema.kind} that the run holds does not encode`);
    return json.encoded;
  }

  unordered(schema: Schema, value: unknown): unknown {
    const shape = this.shape(schema);
    return attempt(() => orderFree(comparableOf(shape, value)), schema);
  }

  decode(schema: Schema, value: Json): Fields {
    return decoded(objectOf(this.shape(schema)), value) as Fields;
  }

  binding(
    name: string,
    binding: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    return this.nonNullBinding(this.command(name).binds, binding, { input, records: this.view(records), now });
  }

  requirement(
    name: string,
    condition: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    const command = this.command(name);
    return this.boundHolds(command.binds, command.requires, condition, { input, records: this.view(records), now });
  }

  inputRequirement(target: DefinitionRef, condition: string, input: Fields): boolean | Failed {
    type Requiring = { readonly requires?: Conditions<{ input: Fields }> };
    const conditions = this.definition<Requiring>(["command", "query", "screen"], target).definition.requires;
    const f = named(conditions, condition, "requires condition");
    return attempt(() => Boolean(f({ input })));
  }

  /**
   * Returns the ref of an event that decide emits. An event value that is no named definition of the spec gets a ref
   * that names no definition, which the run reports as an unlisted emitted event.
   */
  private emittedRef(event: unknown): DefinitionRef {
    const named = this.spec.names.get(event);
    return named === undefined ? { service: this.service, name: "?" } : { service: named.service, name: named.name };
  }

  decide(
    name: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): readonly (readonly Decided[])[] | Failed {
    const command = this.command(name);
    const args = { input, records: this.view(records), now };
    const bound = this.bound(command.binds, args);
    if (bound instanceof Failed) return bound;
    const f = command.decide as ((a: Fields) => readonly (DefinedEmit | Bag<DefinedEmit>)[]) | undefined;
    if (f === undefined) throw new InternalError(`the command ${name} of an external service has no decide`);
    const decided = attempt(() =>
      f({ ...args, bound }).map((item) => (bagValues(item) ?? [item]) as readonly DefinedEmit[]),
    );
    if (decided instanceof Failed) return decided;
    const groups: Decided[][] = [];
    for (const group of decided) {
      const encoded: Decided[] = [];
      for (const e of group) {
        const event = this.emittedRef(e.event);
        const payload = lists(this.st, name, { event })
          ? encodedAnswer({ kind: "payload", event }, strictObjectOf(e.event.payload), e.payload)
          : null;
        if (payload instanceof Failed) return payload;
        encoded.push({ event, payload });
      }
      groups.push(encoded);
    }
    return groups;
  }

  ensures(
    name: string,
    input: Fields,
    before: RecordSource,
    after: RecordSource,
    now: Temporal.Instant,
  ): string | undefined | Failed {
    const command = this.command(name);
    return attempt(() =>
      firstFailing(command.ensures as Conditions<Fields>, () => {
        const bound = this.bound(command.binds, { input, records: this.view(before), now });
        if (bound instanceof Failed) throw bound;
        return { input, records: this.view(after), bound };
      }),
    );
  }

  queryEnsures(name: string, input: Fields, output: Fields, records: RecordSource): string | undefined | Failed {
    const query = this.query(name).definition;
    return attempt(() =>
      firstFailing(query.ensures as Conditions<Fields>, () => ({ input, output, records: this.view(records) })),
    );
  }

  /**
   * Returns what one ensures of a request's target gives on the request's results. `output` counts only when the target
   * has an output schema; a query's results have no events.
   */
  resultEnsures(
    request: DefinitionRef,
    condition: string,
    input: Fields,
    output: unknown,
    events: readonly Emit[],
  ): Ensured | Failed {
    const target = this.definition<AnyCommand | AnyQuery>(["command", "query"], request).definition;
    const emits = events.map(
      (e): DefinedEmit => ({
        kind: "emit",
        event: this.definition<AnyEvent>(["event"], e.event).definition,
        payload: e.payload as never,
      }),
    );
    const results = {
      input,
      ...(target.output === undefined ? {} : { output }),
      ...(target.kind === "query" ? {} : { events: emits }),
    };
    const f = named(target.ensures as Conditions<unknown>, condition, "ensures condition");
    return attempt(() => ensured(f, results));
  }

  invariant(entity: string, record: Fields): string | undefined | Failed {
    const conditions = this.entity(entity).invariants as Conditions<{ readonly record: Fields }>;
    return attempt(() => firstFailing(conditions, () => ({ record })));
  }

  serviceInvariant(records: RecordSource): string | undefined | Failed {
    const conditions = this.ownerDefinition().invariants as Conditions<{ records: unknown }>;
    return attempt(() => firstFailing(conditions, () => ({ records: this.view(records) })));
  }

  chartInvariant(scope: Scope, records: RecordSource, access: Access): string | undefined | Failed {
    const invariants = this.chartOf(chartOf(scope.id)).named.definition.invariants;
    return attempt(() => firstFailing(invariants, () => this.args(scope, records, access)));
  }

  resolve(name: string, input: Fields, records: RecordSource, now: Temporal.Instant): Json | Failed {
    const { definition: query, service } = this.query(name);
    const resolved = attempt(() =>
      (query.resolve as (a: unknown) => unknown)({ input, records: this.view(records), now }),
    );
    if (resolved instanceof Failed) return resolved;
    const schema: Schema = { kind: "output", definition: { service, name } };
    return encodedAnswer(schema, strictObjectOf(expectFound(`the output of ${name}`, query.output)), resolved);
  }

  private automation(name: string): Automation {
    return this.own<Automation>(["automation"], name).definition;
  }

  automationBinding(
    name: string,
    binding: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    return this.nonNullBinding(this.automation(name).binds, binding, { payload, records: this.view(records), now });
  }

  automationGuard(
    name: string,
    condition: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    const a = this.automation(name);
    return this.boundHolds(a.binds, a.guard, condition, { payload, records: this.view(records), now });
  }

  react(
    name: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
    keys: Keys,
  ): { readonly input: Json; readonly created: readonly string[] } | Failed {
    const a = this.automation(name);
    const { createKey, created } = this.keysFrom(keys);
    const args = { payload, records: this.view(records), now };
    const values = this.bound(a.binds, args);
    if (values instanceof Failed) return values;
    const [command, ...more] = Object.values(a.commands);
    if (command === undefined || more.length > 0) throw new InternalError(`the automation ${name} has no one command`);
    const input = a.input;
    const given = attempt(() => (input === undefined ? {} : input({ ...args, bound: values, createKey } as never)));
    if (given instanceof Failed) return given;
    const target = expectFound(
      `automation ${name}`,
      this.st.automations.find((x) => x.name === name),
    ).sends.target;
    const json = encodedAnswer({ kind: "input", definition: target }, strictObjectOf(command.input), given);
    return json instanceof Failed ? json : { input: json, created };
  }

  comparable(name: string, answer: Answer): unknown {
    const found = this.query(name);
    const schema: Schema = { kind: "output", definition: { service: found.service, name: found.name } };
    return attempt(() => orderFree(comparableAnswer(answer, found.definition.output)), schema);
  }

  initialContext(machine: string, input: Fields): Json | Failed {
    const { named, ref } = this.chartOf(machine);
    const f = named.definition.initialContext;
    const given = attempt(() => (f === undefined ? {} : f({ input })));
    if (given instanceof Failed) return given;
    return encodedAnswer({ kind: "context", chart: ref }, strictObjectOf(named.definition.context).partial(), given);
  }

  defaults(schema: Schema): Json | Failed {
    const shape = this.shape(schema);
    const row = attempt(() => defaultRow(shape), schema);
    return row instanceof Failed ? row : encodedAnswer(schema, strictObjectOf(shape), row);
  }

  guard(
    scope: Scope,
    records: RecordSource,
    transition: TransitionRef,
    condition: string,
    extra: Fields,
    access: Access,
  ): boolean | Failed {
    const f = named(this.transition(chartOf(scope.id), transition).guard, condition, "guard condition");
    return attempt(() => Boolean(f(this.args(scope, records, access, extra) as never)));
  }

  /**
   * Returns the contexts after the assignment, and tells `access` the assigned fields once both contexts match their
   * schemas.
   */
  assign(
    scope: Scope,
    records: RecordSource,
    assignment: Assignment,
    extra: Fields,
    keys: Keys,
    access: Access,
  ): { readonly context: Json; readonly copyContext: Json | undefined; readonly created: readonly string[] } | Failed {
    const { named, ref } = this.chartOf(chartOf(scope.id));
    const copy = scope.copy;
    const map = mapOf(scope.id);
    const shape = map === undefined ? {} : (this.mapNode(chartOf(scope.id), map).context ?? {});
    const assignments = this.assignments(chartOf(scope.id), assignment);
    const { createKey, created } = this.keysFrom(keys);
    let assigned: readonly (readonly [string, unknown])[] = [];
    if (assignments !== undefined) {
      const args = this.args(scope, records, access, { ...extra, createKey });
      const values = attempt(() => Object.entries(assignments).map(([field, f]) => [field, f(args)] as const));
      if (values instanceof Failed) return values;
      assigned = values;
    }
    const [own, outer] = [assigned.filter(([f]) => f in shape), assigned.filter(([f]) => !(f in shape))];
    let copyContext: Json | undefined;
    if (copy !== undefined) {
      const schema: Schema = { kind: "mapContext", chart: ref, map: map as string };
      const checked = encodedAnswer(schema, strictObjectOf(shape), { ...copy.context, ...Object.fromEntries(own) });
      if (checked instanceof Failed) return checked;
      copyContext = checked;
    }
    const context = encodedAnswer({ kind: "context", chart: ref }, strictObjectOf(named.definition.context), {
      ...scope.context,
      ...Object.fromEntries(outer),
    });
    if (context instanceof Failed) return context;
    for (const [field] of own) access.assigned("copy", field);
    for (const [field] of outer) access.assigned("owner", field);
    return { context, copyContext, created };
  }

  /** Returns the checked input of a request or an opened screen; only a sends input may call createKey. */
  input(
    scope: Scope,
    records: RecordSource,
    activity: Activity,
    keys: Keys,
    access: Access,
  ): { readonly input: Json; readonly created: readonly string[] } | Failed {
    const chart = this.chartOf(chartOf(scope.id)).named.definition;
    const node = this.node(chartOf(scope.id), this.stateOf(scope));
    const { createKey, created } = this.keysFrom(keys);
    const args = () => this.args(scope, records, access);
    const { key } = activity;
    let given: Json | Failed;
    switch (activity.keyword) {
      case "shows": {
        const shown = this.showInput(scope, records, activity, access);
        return shown instanceof Failed ? shown : { input: shown, created };
      }
      case "calls": {
        given = this.writtenInput(
          activity.target,
          named(chart.queries, key, "query").input,
          node.calls?.[key]?.input,
          args,
        );
        break;
      }
      case "sends":
        given = this.writtenInput(
          activity.target,
          named(chart.commands, key, "command").input,
          node.sends?.[key]?.input,
          () => this.args(scope, records, access, { createKey }),
        );
        break;
      case "opens": {
        given = this.writtenInput(
          activity.target,
          named(chart.screens, key, "screen").input ?? {},
          node.opens?.[key]?.input,
          args,
        );
      }
    }
    return given instanceof Failed ? given : { input: given, created };
  }

  /** Returns the parameters of `state` that `edge`'s `with` fills, encoded by the state's held schema. */
  held(scope: Scope, records: RecordSource, state: string, edge: Edge, extra: Fields, access: Access): Json | Failed {
    const machine = chartOf(scope.id);
    const fills = (
      edge.kind === "transition"
        ? this.transition(machine, edge.transition).with
        : this.node(machine, edge.parent).initialWith
    ) as Assignments | undefined;
    const ref = this.chartOf(machine).ref;
    const args = this.args(scope, records, access, extra);
    const shape = this.shape({ kind: "held", chart: ref, state });
    const values = attempt(() =>
      Object.fromEntries(Object.keys(shape).map((name) => [name, named(fills, name, "with parameter")(args)])),
    );
    if (values instanceof Failed) return values;
    return encodedAnswer({ kind: "held", chart: ref, state }, strictObjectOf(shape), values);
  }

  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access): string | undefined | Failed {
    const d = named(this.node(chartOf(scope.id), this.stateOf(scope)).after, name, "deadline");
    const at = d.at as ((args: unknown) => unknown) | undefined;
    if (at === undefined) throw new InternalError(`the deadline ${name} has no at`);
    const time = attempt(() => at(this.args(scope, records, access)));
    if (time instanceof Failed) return time;
    return time instanceof Temporal.Instant ? time.toString() : undefined;
  }

  /** Returns the offers of the state `scope.state`, or of the chart itself when it is null. */
  offers(scope: Scope, records: RecordSource, control: string, access: Access): readonly Json[] | Failed {
    const { named, ref } = this.chartOf(chartOf(scope.id));
    const f =
      scope.state === null
        ? named.definition.offers?.[control]
        : this.node(chartOf(scope.id), scope.state).offers?.[control];
    // Lean asks only for the offers that a function lists.
    if (typeof f !== "function") throw new InternalError(`the offers of ${control} list no payloads`);
    const given = attempt(() => f(this.args(scope, records, access) as never));
    if (given instanceof Failed) return given;
    const payloads = bagValues(given) ?? (given as readonly unknown[]);
    const row = strictObjectOf(this.control(named.definition, control).payload ?? {});
    const checked: Json[] = [];
    for (const o of payloads) {
      const payload = encodedAnswer({ kind: "control", screen: ref, control }, row, o);
      if (payload instanceof Failed) return payload;
      checked.push(payload);
    }
    return checked;
  }

  showInput(scope: Scope, records: RecordSource, { key, target }: Activity, access: Access): Json | Failed {
    const query = named(this.chartOf(chartOf(scope.id)).named.definition.queries, key, "query");
    const f = this.node(chartOf(scope.id), this.stateOf(scope)).shows?.[key]?.input;
    return this.writtenInput(target, query.input, f, () => this.args(scope, records, access));
  }

  items(scope: Scope, records: RecordSource, access: Access): readonly Json[] | Failed {
    const map = this.stateOf(scope);
    const node = this.mapNode(chartOf(scope.id), map);
    const given = attempt(() => node.items(this.args(scope, records, access) as never));
    if (given instanceof Failed) return given;
    const chart = this.chartOf(chartOf(scope.id)).ref;
    const keys = encodedAnswer({ kind: "mapKey", chart, map }, bag(strictObjectOf(node.key)), given);
    return keys instanceof Failed ? keys : (keys as readonly Json[]);
  }

  close(scope: Scope, records: RecordSource, access: Access): Json | Failed {
    const { named, ref } = this.chartOf(chartOf(scope.id));
    const chart = named.definition;
    const resolve = chart.resolve;
    const given = attempt(() => (resolve === undefined ? {} : resolve(this.args(scope, records, access) as never)));
    if (given instanceof Failed) return given;
    return encodedAnswer({ kind: "output", definition: ref }, strictObjectOf(chart.output ?? {}), given);
  }

  closeEnsures(screen: string, input: Fields, output: Fields): string | undefined | Failed {
    const chart = this.chartOf(screen).named.definition;
    return attempt(() => firstFailing(chart.ensures, () => ({ input, output })));
  }
}
