import { z } from "zod";
import { type Bag, bagValues, NotOnly } from "../../data/bag.ts";
import { comparableAnswer, comparable as comparableOf, orderFree } from "../../data/canonical.ts";
import { bag, bagged, defaultRow, sorted, toJson, written } from "../../data/collections.ts";
import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { Ensured } from "../../data/ensured.generated.ts";
import type { Activity } from "../../data/step.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import type { TransitionRef } from "../../data/transitionRef.generated.ts";
import { canonicalJson, type Fields, type Json, objectOf, type Shape, strictObjectOf } from "../../data/values.ts";
import { thrown, zodError } from "../../data/violation.ts";
import { stateAt, transitionAt } from "../../dsl/chart.ts";
import { type Conditions, firstFailing } from "../../dsl/conditions.ts";
import type {
  AnyCommand,
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
  type Edge,
  Failed,
  type Functions,
  givenKeys,
  type Holder,
  type Keys,
  type Scope,
} from "../../service/functions.ts";
import { chartOf, mapOf } from "../../service/instance.ts";
import type { Emit } from "../../service/message.ts";
import type { RecordSource, Row } from "../../service/records.ts";
import { type ChartStructure, chartStructure, stateNamed } from "../../spec/structure.ts";
import { isDescendant } from "../../spec/tree.ts";
import { ensured } from "./contract.ts";
import { recordsView } from "./records.ts";

// Every `input` and `payload` argument here is a decoded value.

/**
 * Runs author code and returns its value. A throw becomes a `thrown` Issue, of `schema` when the code is that schema's
 * refinement or codec; the Issue of a held read inside passes through, and `only()` on more than one value is notOnly.
 */
function attempt<T>(f: () => T, schema?: Schema): T | Failed {
  try {
    return f();
  } catch (error) {
    if (error instanceof Failed) return error;
    if (error instanceof NotOnly) return new Failed({ kind: "notOnly" });
    return new Failed(schema === undefined ? { kind: "thrown" } : { kind: "thrown", schema }, thrown(error));
  }
}

/**
 * Returns a value that author code made, with each Bag in a bag, set or sortedBy field as an array, as Lean's Value can
 * hold it for normalize.
 */
const sortedFields = (shape: Shape | undefined, value: unknown): unknown => sorted(objectOf(shape ?? {}), value);

/**
 * Returns the value with every collection sorted, as spec code receives it, and its encoding, or why it does not match
 * `zod`.
 */
function encodedSorted<T>(
  schema: Schema,
  zod: z.ZodType,
  value: T,
): { readonly value: T; readonly encoded: unknown } | { readonly error: z.ZodError } | Failed {
  const checked = attempt(() => {
    const sortedValue = sorted(zod, value) as T;
    return { sortedValue, encoded: z.safeEncode(zod, sortedValue as never) };
  }, schema);
  if (checked instanceof Failed) return checked;
  const { sortedValue, encoded } = checked;
  return encoded.success ? { value: bagged(zod, sortedValue) as T, encoded: encoded.data } : { error: encoded.error };
}

/** Returns the checked value and its encoding, or the Issue of a value that does not match `schema`. */
function matching<T>(
  schema: Schema,
  zod: z.ZodType,
  value: T,
): { readonly value: T; readonly encoded: unknown } | Failed {
  const checked = encodedSorted(schema, zod, value);
  if (checked instanceof Failed || !("error" in checked)) return checked;
  return new Failed({ kind: "schema", schema }, zodError(checked.error.issues));
}

/** Returns the binds values, which Lean asks for only once every binding is non-null. */
const bound = (binds: Binds<never>, args: Fields): Fields =>
  Object.fromEntries(Object.entries(binds as Binds<Fields>).map(([name, f]) => [name, f(args)]));

const nonNull = (value: unknown): boolean => value !== null && value !== undefined;

/** Returns the function `name` of `functions`, which Lean names from the structure, so that it always exists. */
function named<F>(functions: Readonly<Record<string, F>> | undefined, name: string, what: string): F {
  const f = functions?.[name];
  if (f === undefined) throw new Error(`the definition has no ${what} ${name}`);
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
    throw new Error(`the spec has no ${kinds.join(" or ")} ${r.name} of ${r.service}`);
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
        return (schema.kind === "input" ? found.input : found.output) ?? {};
      }
      case "payload":
        return this.definition<AnyEvent>(["event"], schema.event).definition.payload;
      case "control":
        return (
          this.definition<ChartSpec>(["screen"], schema.screen).definition.controls?.[schema.control]?.payload ?? {}
        );
      case "record":
        return this.definition<AnyEntity>(["entity"], schema.entity).definition.fields as Shape;
      case "context":
        return this.chartOf(schema.chart.name).named.definition.context;
      case "mapContext":
        return this.node(schema.chart.name, schema.map).context ?? {};
      case "held": {
        const field = this.node(schema.chart.name, schema.state).held?.[schema.name];
        if (field === undefined) throw new Error(`the state ${schema.state} has no parameter ${schema.name}`);
        return { [schema.name]: field };
      }
      default:
        throw new Error(`no question checks a value of the ${schema.kind} schema`);
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
    if (structure === undefined) throw new Error(`the spec has no structure of the chart ${name}`);
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
    if (found === undefined) throw new Error(`the chart ${machine} has no state ${state}`);
    const node = stateAt(named.definition, found.path);
    nodes.set(state, node);
    return node;
  }

  /** Returns the state that declares the expressions of a question that Lean always asks about a state. */
  private stateOf(scope: Scope): string {
    if (scope.state === null) throw new Error(`a question about ${chartOf(scope.id)} names no state`);
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
    if (found === undefined) throw new Error(`the service ${this.service} has no entity ${name}`);
    return found as AnyEntity;
  }

  /** Returns the service definition, which every question that reads records or entities has. */
  private ownerDefinition(): ServiceDefinition {
    if (this.owner === undefined) throw new Error(`the spec has no service ${this.service}`);
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
      created.push(this.spec.names.get(refTarget(key))?.name ?? "id");
      return givenKeys(keys, created).at(-1)?.[1] as string;
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

  /** Returns the input that `f` gives a request or screen of the input shape `shape`, as the sender writes it. */
  private writtenInput(shape: Shape, f: ((args: never) => unknown) | undefined, args: () => Fields): Json | Failed {
    return attempt(() => written(objectOf(shape), f?.(args() as never) ?? {}));
  }

  /** Returns the binds values, which every binding answered non-null before. */
  private bound(binds: Binds<never>, args: Fields): Fields | Failed {
    return attempt(() => bound(binds, args));
  }

  parse(schema: Schema, value: unknown): Checked | Failed {
    // Given writes every field of a record, so a record also fails on a field that its entity does not have.
    const object = schema.kind === "record" ? strictObjectOf(this.shape(schema)) : objectOf(this.shape(schema));
    const parsed = attempt(() => object.safeParse(value), schema);
    if (parsed instanceof Failed) return parsed;
    if (!parsed.success) return { error: zodError(parsed.error.issues) };
    return { value: bagged(object, parsed.data) as Fields, encoded: toJson(object, parsed.data) };
  }

  /** Returns a decoded value of `schema` as JSON holds it, as Lean holds it (ChoiceDependent's Encode). */
  encode(schema: Schema, value: unknown): Json {
    return written(objectOf(this.shape(schema)), value);
  }

  unordered(schema: Schema, value: unknown): unknown {
    const shape = this.shape(schema);
    return attempt(() => orderFree(comparableOf(shape, value)), schema);
  }

  normalize(schema: Schema, value: unknown): Checked | Failed {
    const checked = encodedSorted(schema, strictObjectOf(this.shape(schema)), value as Fields);
    if (checked instanceof Failed || !("error" in checked)) return checked;
    return { error: zodError(checked.error.issues) };
  }

  binding(name: string, b: string, input: Fields, records: RecordSource, now: Temporal.Instant): boolean | Failed {
    const f = named(this.command(name).binds as Binds<Fields>, b, "binding");
    const value = attempt(() => f({ input, records: this.view(records), now }));
    return value instanceof Failed ? value : nonNull(value);
  }

  requirement(
    name: string,
    condition: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    const command = this.command(name);
    const args = { input, records: this.view(records), now };
    const bound = this.bound(command.binds, args);
    if (bound instanceof Failed) return bound;
    const f = named(command.requires as Conditions<Fields>, condition, "requires condition");
    return attempt(() => Boolean(f({ ...args, bound })));
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
  ): readonly (readonly Emit[])[] | Failed {
    const command = this.command(name);
    const args = { input, records: this.view(records), now };
    const bound = this.bound(command.binds, args);
    if (bound instanceof Failed) return bound;
    const f = command.decide as ((a: Fields) => readonly (DefinedEmit | Bag<DefinedEmit>)[]) | undefined;
    if (f === undefined) throw new Error(`the command ${name} of an external service has no decide`);
    return attempt(() =>
      f({ ...args, bound }).map((item) =>
        ((bagValues(item) ?? [item]) as readonly DefinedEmit[]).map((e) => ({
          event: this.emittedRef(e.event),
          payload: sortedFields(e.event.payload, e.payload) as Fields,
        })),
      ),
    );
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

  resolve(name: string, input: Fields, records: RecordSource, now: Temporal.Instant): unknown {
    const query = this.query(name).definition;
    return attempt(() =>
      sortedFields(
        query.output,
        (query.resolve as (a: unknown) => unknown)({ input, records: this.view(records), now }),
      ),
    );
  }

  private automation(name: string): Automation {
    return this.own<Automation>(["automation"], name).definition;
  }

  automationBinding(
    name: string,
    b: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    const f = named(this.automation(name).binds as Binds<Fields>, b, "binding");
    const value = attempt(() => f({ payload, records: this.view(records), now }));
    return value instanceof Failed ? value : nonNull(value);
  }

  automationGuard(
    name: string,
    condition: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed {
    const a = this.automation(name);
    const args = { payload, records: this.view(records), now };
    const values = this.bound(a.binds, args);
    if (values instanceof Failed) return values;
    const f = named(a.guard as Conditions<Fields>, condition, "guard condition");
    return attempt(() => Boolean(f({ ...args, bound: values })));
  }

  react(
    name: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
    keys: Keys,
  ): { readonly written: Json; readonly created: readonly string[] } | Failed {
    const a = this.automation(name);
    const { createKey, created } = this.keysFrom(keys);
    const args = { payload, records: this.view(records), now };
    const values = this.bound(a.binds, args);
    if (values instanceof Failed) return values;
    const shape = objectOf(a.command.definition.input);
    const given = attempt(() => written(shape, a.input?.({ ...args, bound: values, createKey } as never) ?? {}));
    return given instanceof Failed ? given : { written: given, created };
  }

  comparable(name: string, answer: Answer): unknown {
    const found = this.query(name);
    const schema: Schema = { kind: "output", definition: { service: found.service, name: found.name } };
    return attempt(() => orderFree(comparableAnswer(answer, found.definition.output)), schema);
  }

  /** Returns initialContext with the defaults of the fields that it leaves out. */
  initialContext(machine: string, input: Fields): Fields | Failed {
    const { named, ref } = this.chartOf(machine);
    const chart = named.definition;
    const row = attempt(() => {
      const initial = (chart.initialContext?.({ input }) ?? {}) as Fields;
      const filled: Fields = { ...initial };
      for (const [field, schema] of Object.entries(chart.context)) {
        if (field in initial) continue;
        const defaulted = (schema as z.ZodType).safeParse(undefined);
        if (defaulted.success) filled[field] = defaulted.data;
      }
      return filled;
    });
    if (row instanceof Failed) return row;
    const context = matching({ kind: "context", chart: ref }, strictObjectOf(chart.context), row);
    if (context instanceof Failed) return context;
    return context.value;
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
  ):
    | { readonly context: Fields; readonly copyContext: Fields | undefined; readonly created: readonly string[] }
    | Failed {
    const { named, ref } = this.chartOf(chartOf(scope.id));
    const copy = scope.copy;
    const assignments = this.assignments(chartOf(scope.id), assignment);
    if (assignments === undefined) return { context: scope.context, copyContext: copy?.context, created: [] };
    const { createKey, created } = this.keysFrom(keys);
    const args = this.args(scope, records, access, { ...extra, createKey });
    const assigned = attempt(() => Object.entries(assignments).map(([field, f]) => [field, f(args)] as const));
    if (assigned instanceof Failed) return assigned;
    const map = mapOf(scope.id);
    const shape = map === undefined ? {} : (this.node(chartOf(scope.id), map).context ?? {});
    const [own, outer] = [assigned.filter(([f]) => f in shape), assigned.filter(([f]) => !(f in shape))];
    let copyContext = copy?.context;
    if (copy !== undefined && own.length > 0) {
      const checked = matching({ kind: "mapContext", chart: ref, map: map as string }, strictObjectOf(shape), {
        ...copy.context,
        ...Object.fromEntries(own),
      });
      if (checked instanceof Failed) return checked;
      copyContext = checked.value;
    }
    let context = scope.context;
    if (outer.length > 0) {
      const checked = matching({ kind: "context", chart: ref }, strictObjectOf(named.definition.context), {
        ...scope.context,
        ...Object.fromEntries(outer),
      });
      if (checked instanceof Failed) return checked;
      context = checked.value;
    }
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
  ): { readonly written: Json; readonly created: readonly string[] } | Failed {
    const chart = this.chartOf(chartOf(scope.id)).named.definition;
    const node = this.node(chartOf(scope.id), this.stateOf(scope));
    const { createKey, created } = this.keysFrom(keys);
    const args = () => this.args(scope, records, access);
    const { key } = activity;
    let given: Json | Failed;
    switch (activity.keyword) {
      case "shows": {
        const shown = this.showInput(scope, records, activity, access);
        return shown instanceof Failed ? shown : { written: shown, created };
      }
      case "calls": {
        const query = chart.queries?.[key] as AnyQuery;
        given = this.writtenInput(query.input, node.calls?.[key]?.input, args);
        break;
      }
      case "sends":
        given = this.writtenInput((chart.commands[key] as AnyCommand).input, node.sends?.[key]?.input, () =>
          this.args(scope, records, access, { createKey }),
        );
        break;
      case "opens": {
        given = this.writtenInput(chart.screens?.[key]?.input ?? {}, node.opens?.[key]?.input, args);
      }
    }
    return given instanceof Failed ? given : { written: given, created };
  }

  /** Returns the parameters of `state` that `edge`'s `with` fills, each checked against its held schema. */
  held(scope: Scope, records: RecordSource, state: string, edge: Edge, extra: Fields, access: Access): Fields | Failed {
    const machine = chartOf(scope.id);
    const fills = (
      edge.kind === "transition"
        ? this.transition(machine, edge.transition).with
        : this.node(machine, edge.parent).initialWith
    ) as Assignments | undefined;
    const ref = this.chartOf(machine).ref;
    const args = this.args(scope, records, access, extra);
    const values: Record<string, unknown> = {};
    for (const [name, schema] of Object.entries(this.node(machine, state).held ?? {})) {
      const value = attempt(() => fills?.[name]?.(args));
      if (value instanceof Failed) return value;
      const checked = matching({ kind: "held", chart: ref, state, name }, schema as z.ZodType, value);
      if (checked instanceof Failed) return checked;
      values[name] = checked.value;
    }
    return values;
  }

  deadlines(machine: string, state: string): readonly string[] {
    return Object.keys(this.node(machine, state).after ?? {});
  }

  deadlineTime(scope: Scope, records: RecordSource, name: string, access: Access): string | undefined | Failed {
    const d = named(this.node(chartOf(scope.id), this.stateOf(scope)).after, name, "deadline");
    const at = d.at as ((args: unknown) => unknown) | undefined;
    if (at === undefined) {
      if (d.delay === undefined) throw new Error(`the deadline ${name} has neither delay nor at`);
      return scope.now.add(d.delay).toString();
    }
    const time = attempt(() => at(this.args(scope, records, access)));
    if (time instanceof Failed) return time;
    return time instanceof Temporal.Instant ? time.toString() : undefined;
  }

  /** Returns the offers of the state `scope.state`, or of the chart itself when it is null. */
  offers(
    scope: Scope,
    records: RecordSource,
    control: string,
    access: Access,
  ): readonly { readonly value: Fields; readonly encoded: unknown }[] | Failed {
    const { named, ref } = this.chartOf(chartOf(scope.id));
    const f =
      scope.state === null
        ? named.definition.offers?.[control]
        : this.node(chartOf(scope.id), scope.state).offers?.[control];
    // Lean asks only for the offers that a function lists.
    if (typeof f !== "function") throw new Error(`the offers of ${control} list no payloads`);
    const given = attempt(() => f(this.args(scope, records, access) as never));
    if (given instanceof Failed) return given;
    const payloads = bagValues(given) ?? (given as readonly unknown[]);
    const row = strictObjectOf(named.definition.controls?.[control]?.payload ?? {});
    const checked: { readonly value: Fields; readonly encoded: unknown }[] = [];
    for (const o of payloads) {
      const payload = matching({ kind: "control", screen: ref, control }, row, o as Fields);
      if (payload instanceof Failed) return payload;
      checked.push(payload);
    }
    return checked;
  }

  showInput(scope: Scope, records: RecordSource, { key }: Activity, access: Access): Json | Failed {
    const query = this.chartOf(chartOf(scope.id)).named.definition.queries?.[key] as AnyQuery;
    const f = this.node(chartOf(scope.id), this.stateOf(scope)).shows?.[key]?.input;
    return this.writtenInput(query.input, f, () => this.args(scope, records, access));
  }

  items(
    scope: Scope,
    records: RecordSource,
    access: Access,
  ): readonly { readonly key: unknown; readonly encoded: unknown; readonly encodedKey: string }[] | Failed {
    const map = this.stateOf(scope);
    const node = this.node(chartOf(scope.id), map);
    const items = node.items;
    if (items === undefined) throw new Error(`the map state ${map} has no items`);
    const given = attempt(() => items(this.args(scope, records, access) as never));
    if (given instanceof Failed) return given;
    const chart = this.chartOf(chartOf(scope.id)).ref;
    const element = objectOf(node.key ?? {});
    const keys = matching({ kind: "mapKey", chart, map }, bag(element), given);
    if (keys instanceof Failed) return keys;
    // Each key is decoded from its encoding, because the Bag of keys visits them in reverse order inside reversedBags.
    return (keys.encoded as unknown[]).map((encoded) => ({
      key: bagged(element, z.decode(element, encoded as never)),
      encoded,
      encodedKey: canonicalJson(encoded),
    }));
  }

  /** Returns the defaults of the map state's copy context, which load checks against the schema. */
  copyContext(machine: string, map: string): Fields {
    const shape = this.node(machine, map).context ?? {};
    return bagged(objectOf(shape), defaultRow(shape)) as Fields;
  }

  /** Returns the defaults of a single entity's fields, which load checks against the schema. */
  singleRecord(entity: string): Row {
    const shape = this.entity(entity).fields as Shape;
    const value = defaultRow(shape);
    return { value: bagged(objectOf(shape), value) as Fields, encoded: toJson(objectOf(shape), value) as Fields };
  }

  copyKey(machine: string, map: string, payload: unknown): string | null | undefined | Failed {
    const shape = this.node(machine, map).key ?? {};
    const fields = Object.keys(shape);
    const row = payload as Fields;
    if (!fields.every((f) => row[f] !== undefined)) return undefined;
    const key = sorted(objectOf(shape), Object.fromEntries(fields.map((f) => [f, row[f]])));
    const chart = this.chartOf(machine).ref;
    const encoded = attempt(() => z.safeEncode(objectOf(shape), key as never), { kind: "mapKey", chart, map });
    if (encoded instanceof Failed) return encoded;
    return encoded.success ? canonicalJson(encoded.data) : null;
  }

  close(
    scope: Scope,
    records: RecordSource,
    access: Access,
  ): { readonly output: Fields; readonly failed: string | undefined } | Failed {
    const { named, ref } = this.chartOf(chartOf(scope.id));
    const chart = named.definition;
    const given = attempt(() => chart.resolve?.(this.args(scope, records, access) as never) ?? {});
    if (given instanceof Failed) return given;
    const output = matching({ kind: "output", definition: ref }, strictObjectOf(chart.output ?? {}), given as Fields);
    if (output instanceof Failed) return output;
    const failed = attempt(() => firstFailing(chart.ensures, () => ({ input: scope.input, output: output.value })));
    if (failed instanceof Failed) return failed;
    return { output: output.value, failed };
  }
}
