import { z } from "zod";
import { assumedEnsures } from "../contract/checks.ts";
import { NotOnly, valuesOf } from "../data/bag.ts";
import { canonical as canonicalOf, comparableAnswer, orderFree } from "../data/canonical.ts";
import { bag, bagged, defaultRow, sorted } from "../data/collections.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Answer } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.ts";
import { canonicalJson, encode, type Fields, objectOf, type Shape, strictObjectOf } from "../data/values.ts";
import { thrown, zodError } from "../data/violation.ts";
import { stateAt, transitionAt } from "../dsl/chart.ts";
import { type Conditions, firstFailing } from "../dsl/conditions.ts";
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
} from "../dsl/definition.ts";
import { type AnyEntity, type AnyKeyedEntity, type Ref, refTarget } from "../dsl/entity.ts";
import type { Spec } from "../load/load.ts";
import { refOfDefinition, traceName } from "../load/traceName.ts";
import {
  type Access,
  type Assignment,
  type Checked,
  type DeadlineTime,
  Failed,
  type Functions,
  type Holder,
  type Scope,
} from "../semantics/functions.ts";
import type { Emit } from "../semantics/message.ts";
import type { Note } from "../semantics/note.ts";
import { type Schema, type Service, serviceOf } from "../semantics/service/basic.ts";
import type { RecordSource, Row } from "../semantics/service/records.ts";
import { type ChartStructure, chartStructure, stateNamed, traceNameOfRef } from "../syntax/structure.ts";
import { isDescendant, pathOf } from "../syntax/tree.ts";
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
const unbagged = (shape: Shape | undefined, value: unknown): unknown => sorted(objectOf(shape ?? {}), value);

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

/** Returns the binds values in order, up to the first that is null (`unbound`); `reached` hears each. */
function bind(
  binds: Binds<never>,
  args: Fields,
  reached: (binding: string, met: boolean) => void,
): { readonly bound: Fields; readonly unbound?: string } {
  const bound: Fields = {};
  for (const [name, f] of Object.entries(binds as Binds<Fields>)) {
    const value = f(args);
    reached(name, value !== null && value !== undefined);
    if (value === null || value === undefined) return { bound, unbound: name };
    bound[name] = value;
  }
  return { bound };
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

/** Returns the value that `state` holds as `name`, checked against its held schema. */
function heldValue(definition: DefinitionRef, chart: ChartSpec, state: string, name: string, args: unknown): unknown {
  const value = attempt(() => chart.holds?.[state]?.[name]?.(args));
  if (value instanceof Failed) return value;
  const schema = chart.held?.[state]?.[name] as z.ZodType;
  const checked = matching({ kind: "held", chart: definition, state, name }, schema, value);
  return checked instanceof Failed ? checked : checked.value;
}

/**
 * Returns `held` of the expressions written at `path` (the state names from a child of root down to the state where the
 * expression is written), whose holds read `base`. Reading a name throws its Issue when no enclosing state holds the
 * name or the value fails its schema.
 */
function heldOf(definition: DefinitionRef, chart: ChartSpec, path: readonly string[], base: Fields): object {
  return new Proxy(
    {},
    {
      get: (_, name) => {
        if (typeof name !== "string") return undefined;
        const state = path.findLast((n) => chart.holds?.[n]?.[name] !== undefined);
        if (state === undefined) throw new Failed({ kind: "unheld", held: name });
        const value = heldValue(definition, chart, state, name, base);
        if (value instanceof Failed) throw value;
        return value;
      },
    },
  );
}

type Assignments = Readonly<Record<string, (args: unknown) => unknown>>;

/** A machine or screen with its structure, and the nodes of its states as they are looked up. */
interface ChartOf {
  readonly named: Named<ChartSpec>;
  readonly ref: DefinitionRef;
  readonly structure: ChartStructure;
  readonly nodes: Map<string, StateSpec | undefined>;
}

/**
 * The definitions of a service's spec by kind and trace name as seen from the service, its charts, and the view of the
 * service that semantics reads.
 */
interface Index {
  readonly definitions: ReadonlyMap<Definition["kind"], ReadonlyMap<string, Named<Definition>>>;
  readonly charts: Map<string, ChartOf>;
  readonly st: Service;
}

const indexes = new WeakMap<Spec, Map<string, Index>>();

function indexOf(spec: Spec, service: string): Index {
  const byService = indexes.get(spec) ?? new Map<string, Index>();
  indexes.set(spec, byService);
  const known = byService.get(service);
  if (known !== undefined) return known;
  const definitions = new Map<Definition["kind"], Map<string, Named<Definition>>>();
  for (const named of spec.definitions) {
    const byName = definitions.get(named.definition.kind) ?? new Map<string, Named<Definition>>();
    definitions.set(named.definition.kind, byName);
    byName.set(traceName(spec, named.definition, service), named);
  }
  const index = { definitions, charts: new Map<string, ChartOf>(), st: serviceOf(spec.structure, service) };
  byService.set(service, index);
  return index;
}

/** The spec functions of `service`, which answer Lean's questions; react's coverage hits go to `note`. */
export class SpecFunctions implements Functions {
  readonly st: Service;
  private readonly spec: Spec;
  private readonly service: string;
  private readonly owner: ServiceDefinition | undefined;
  private readonly index: Index;
  private readonly note: Pick<Note, "reached"> | undefined;

  constructor(spec: Spec, service: string, note?: Pick<Note, "reached">) {
    this.spec = spec;
    this.service = service;
    this.owner = spec.services.get(service)?.definition;
    this.index = indexOf(spec, service);
    this.st = this.index.st;
    this.note = note;
  }

  /** Returns the definition of one of `kinds` that `name`, a trace name as seen from the service, names. */
  definition<D>(kinds: readonly Definition["kind"][], name: string): Named<D> {
    for (const kind of kinds) {
      const found = this.index.definitions.get(kind)?.get(name);
      if (found !== undefined) return found as Named<D>;
    }
    throw new Error(`the spec has no ${kinds.join(" or ")} named ${name}`);
  }

  /** Returns the shape of the values that `schema` checks: an input, output, payload or control payload. */
  shape(schema: Schema): Shape {
    switch (schema.kind) {
      case "input":
      case "output": {
        const found = this.definition<{ readonly input?: Shape; readonly output?: Shape }>(
          ["command", "query", "screen"],
          traceNameOfRef(schema.definition, this.service),
        ).definition;
        return (schema.kind === "input" ? found.input : found.output) ?? {};
      }
      case "payload":
        return this.definition<AnyEvent>(["event"], traceNameOfRef(schema.event, this.service)).definition.payload;
      case "control":
        return (
          this.chartOf(traceNameOfRef(schema.screen, this.service)).named.definition.controls?.[schema.control]
            ?.payload ?? {}
        );
      default:
        throw new Error(`no question checks a value of the ${schema.kind} schema`);
    }
  }

  private command(name: string): AnyCommand {
    return this.definition<AnyCommand>(["command"], name).definition;
  }

  private query(name: string): Named<AnyQuery> {
    return this.definition<AnyQuery>(["query"], name);
  }

  private request(name: string): AnyCommand | AnyQuery {
    return this.definition<AnyCommand | AnyQuery>(["command", "query"], name).definition;
  }

  /** Returns the machine or screen that `name`, a trace name as seen from the service, names. */
  chartOf(name: string): ChartOf {
    const known = this.index.charts.get(name);
    if (known !== undefined) return known;
    const named = this.definition<ChartSpec>(["machine", "screen"], name);
    const structure = chartStructure(this.spec.structure, named.service, named.name);
    if (structure === undefined) throw new Error(`the spec has no structure of the chart ${name}`);
    const chart = { named, ref: { service: named.service, name: named.name }, structure, nodes: new Map() };
    this.index.charts.set(name, chart);
    return chart;
  }

  node(machine: string, state: string): StateSpec | undefined {
    const { named, structure, nodes } = this.chartOf(machine);
    if (!nodes.has(state)) {
      const found = stateNamed(structure, state);
      nodes.set(state, found === undefined ? undefined : stateAt(named.definition, found.path));
    }
    return nodes.get(state);
  }

  /** Returns the state that declares the expressions of a question that Lean always asks about a state. */
  private stateOf(scope: Scope): string {
    if (scope.state === null) throw new Error(`a question about ${scope.machine} names no state`);
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
        return this.node(machine, assignment.state)?.entry?.assign as Assignments | undefined;
      case "exit":
        return this.node(machine, assignment.state)?.exit?.assign as Assignments | undefined;
    }
  }

  private entity(name: string): AnyEntity {
    return this.owner?.entities[name] as AnyEntity;
  }

  private view(records: RecordSource): Record<string, unknown> {
    return recordsView(this.owner?.entities ?? {}, records);
  }

  /** Returns createKey over the key counts `keys`, and the entities that it was called for, in call order. */
  private keysFrom(keys: readonly (readonly [string, number])[]): {
    readonly createKey: (key: Ref<AnyKeyedEntity>) => string;
    readonly created: readonly string[];
  } {
    const counts = new Map(keys);
    const created: string[] = [];
    const createKey = (key: Ref<AnyKeyedEntity>) => {
      const entity = this.spec.names.get(refTarget(key))?.name ?? "id";
      const n = (counts.get(entity) ?? 0) + 1;
      counts.set(entity, n);
      created.push(entity);
      return `${entity}-${n}`;
    };
    return { createKey, created };
  }

  /**
   * Returns the arguments that every expression of a Scope receives. Building active or records copies every state or
   * record, so they are built only when an expression reads them.
   */
  private baseArgs(scope: Scope, records: RecordSource, access: Access): Fields {
    const { structure } = this.chartOf(scope.machine);
    const copy = scope.copy;
    const context = copy === undefined ? scope.context : { ...scope.context, ...copy.context };
    const holder = (field: string): Holder =>
      copy !== undefined && Object.hasOwn(copy.context, field) ? "copy" : "owner";
    const inCopy = (state: string) =>
      copy !== undefined && state !== copy.map && isDescendant(structure, state, copy.map);
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

  /** Returns the arguments of the expressions written in `scope.state`: the base arguments, `held` and `extra`. */
  private args(scope: Scope, records: RecordSource, access: Access, extra: Fields = {}): Fields {
    const { named, ref, structure } = this.chartOf(scope.machine);
    const base = this.baseArgs(scope, records, access);
    const path = scope.state === null ? [] : pathOf(structure, scope.state);
    return extended(base, { held: heldOf(ref, named.definition, path, base), ...extra });
  }

  /** Returns the input that `f` gives the request or screen `target`, checked against its input schema and encoded. */
  private checkedInput(
    target: DefinitionRef,
    shape: Shape,
    f: ((args: never) => unknown) | undefined,
    args: () => Fields,
  ): { readonly value: Fields; readonly encoded: unknown } | Failed {
    const given = attempt(() => f?.(args() as never) ?? {});
    if (given instanceof Failed) return given;
    return matching({ kind: "input", definition: target }, strictObjectOf(shape), given as Fields);
  }

  /** Returns the binds values, which every binding answered non-null before. */
  private bound(command: AnyCommand, args: Fields): Fields | Failed {
    const binding = attempt(() => bind(command.binds as Binds<never>, args, () => {}));
    return binding instanceof Failed ? binding : binding.bound;
  }

  parse(schema: Schema, value: unknown): Checked | Failed {
    const object = objectOf(this.shape(schema));
    const parsed = attempt(() => object.safeParse(value), schema);
    if (parsed instanceof Failed) return parsed;
    if (!parsed.success) return { error: zodError(parsed.error.issues) };
    const encoded = attempt(() => z.encode(object, parsed.data as never), schema);
    if (encoded instanceof Failed) return encoded;
    return { value: bagged(object, parsed.data) as Fields, encoded };
  }

  canonical(schema: Schema, value: unknown): unknown {
    const shape = this.shape(schema);
    return attempt(() => canonicalOf(shape, value), schema);
  }

  normalize(schema: Schema, value: unknown): Checked | Failed {
    const checked = encodedSorted(schema, strictObjectOf(this.shape(schema)), value as Fields);
    if (checked instanceof Failed || !("error" in checked)) return checked;
    return { error: zodError(checked.error.issues) };
  }

  binding(name: string, b: string, input: Fields, records: RecordSource, now: Temporal.Instant): boolean | Failed {
    const f = (this.command(name).binds as Binds<Fields>)[b];
    const value = attempt(() => f?.({ input, records: this.view(records), now }));
    return value instanceof Failed ? value : value !== null && value !== undefined;
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
    const bound = this.bound(command, args);
    if (bound instanceof Failed) return bound;
    const f = (command.requires as Conditions<Fields>)[condition];
    return attempt(() => Boolean(f?.({ ...args, bound })));
  }

  inputRequirement(target: string, condition: string, input: Fields): boolean | Failed {
    type Requiring = { readonly requires?: Conditions<{ input: Fields }> };
    const f = this.definition<Requiring>(["command", "query", "screen"], target).definition.requires?.[condition];
    return attempt(() => Boolean(f?.({ input })));
  }

  decide(name: string, input: Fields, records: RecordSource, now: Temporal.Instant): readonly Emit[] | Failed {
    const command = this.command(name);
    const args = { input, records: this.view(records), now };
    const bound = this.bound(command, args);
    if (bound instanceof Failed) return bound;
    const f = command.decide as ((a: Fields) => readonly DefinedEmit[]) | undefined;
    return attempt(() =>
      (f?.({ ...args, bound }) ?? []).map((e) => ({
        event: traceName(this.spec, e.event, this.service),
        payload: unbagged(e.event.payload, e.payload) as Fields,
      })),
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
        const bound = this.bound(command, { input, records: this.view(before), now });
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
   * Returns the first failing ensures of a request's result. An ensures that reads records is skipped. `output` counts
   * only when the target has an output schema; a query's results have no events.
   */
  resultEnsures(name: string, input: Fields, output: unknown, events: readonly Emit[]): string | undefined | Failed {
    const target = this.request(name);
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
    return attempt(() => assumedEnsures(target, results));
  }

  invariant(entity: string, record: Fields): string | undefined | Failed {
    const conditions = this.entity(entity).invariants as Conditions<{ readonly record: Fields }>;
    return attempt(() => firstFailing(conditions, () => ({ record })));
  }

  serviceInvariant(records: RecordSource): string | undefined | Failed {
    const conditions = this.owner?.invariants as Conditions<{ records: unknown }>;
    return attempt(() => firstFailing(conditions, () => ({ records: this.view(records) })));
  }

  chartInvariant(scope: Scope, records: RecordSource, access: Access): string | undefined | Failed {
    const invariants = this.chartOf(scope.machine).named.definition.invariants;
    return attempt(() => firstFailing(invariants, () => this.args(scope, records, access)));
  }

  resolve(name: string, input: Fields, records: RecordSource, now: Temporal.Instant): unknown {
    const query = this.query(name).definition;
    return attempt(() =>
      unbagged(query.output, (query.resolve as (a: unknown) => unknown)({ input, records: this.view(records), now })),
    );
  }

  react(
    name: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
    keys: readonly (readonly [string, number])[],
  ): { readonly input?: unknown; readonly created: readonly string[] } | Failed {
    const found = this.definition<Automation>(["automation"], name);
    const a = found.definition;
    const definition = { service: found.service, name: found.name };
    const { createKey, created } = this.keysFrom(keys);
    const reacted = attempt((): { readonly input: unknown } | undefined => {
      const base = { payload, records: this.view(records), now };
      const binding = bind(a.binds, base, (b, met) =>
        this.note?.reached({
          kind: met ? "automationBindingValue" : "automationBindingNull",
          definition,
          data: { binding: b },
        }),
      );
      if (binding.unbound !== undefined) return undefined;
      const args = { ...base, bound: binding.bound };
      for (const [condition, holds] of Object.entries(a.guard as Conditions<typeof args>)) {
        const met = holds(args);
        this.note?.reached({ kind: "automationGuard", definition, data: { condition, met } });
        if (!met) return undefined;
      }
      const command = Object.values(a.commands)[0];
      return { input: unbagged(command?.input, a.input?.({ ...args, createKey } as never) ?? {}) };
    });
    if (reacted instanceof Failed) return reacted;
    return reacted === undefined ? { created } : { input: reacted.input, created };
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

  /** Returns whether the guard holds, and reports a failing condition to `note` as a coverage hit. */
  guard(
    scope: Scope,
    records: RecordSource,
    transition: TransitionRef,
    extra: Fields,
    access: Access,
  ): boolean | Failed {
    const conditions = this.transition(scope.machine, transition).guard;
    const failing = attempt(() => firstFailing(conditions, () => this.args(scope, records, access, extra)));
    if (failing instanceof Failed) return failing;
    if (failing !== undefined)
      this.note?.reached({
        kind: "guardFalse",
        definition: this.chartOf(scope.machine).ref,
        data: { transition, condition: failing },
      });
    return failing === undefined;
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
    keys: readonly (readonly [string, number])[],
    access: Access,
  ):
    | { readonly context: Fields; readonly copyContext: Fields | undefined; readonly created: readonly string[] }
    | Failed {
    const { named, ref } = this.chartOf(scope.machine);
    const copy = scope.copy;
    const assignments = this.assignments(scope.machine, assignment);
    if (assignments === undefined) return { context: scope.context, copyContext: copy?.context, created: [] };
    const { createKey, created } = this.keysFrom(keys);
    const args = this.args(scope, records, access, { ...extra, createKey });
    const assigned = attempt(() => Object.entries(assignments).map(([field, f]) => [field, f(args)] as const));
    if (assigned instanceof Failed) return assigned;
    const shape = copy === undefined ? {} : (this.node(scope.machine, copy.map)?.context ?? {});
    const [own, outer] = [assigned.filter(([f]) => f in shape), assigned.filter(([f]) => !(f in shape))];
    let copyContext = copy?.context;
    if (copy !== undefined && own.length > 0) {
      const checked = matching({ kind: "mapContext", chart: ref, map: copy.map }, strictObjectOf(shape), {
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
    { keyword, key }: { readonly keyword: string; readonly key: string },
    keys: readonly (readonly [string, number])[],
    access: Access,
  ): { readonly value: Fields; readonly encoded: unknown; readonly created: readonly string[] } | Failed {
    const chart = this.chartOf(scope.machine).named.definition;
    const node = this.node(scope.machine, this.stateOf(scope));
    const { createKey, created } = this.keysFrom(keys);
    const args = () => this.args(scope, records, access);
    let checked: { readonly value: Fields; readonly encoded: unknown } | Failed;
    switch (keyword) {
      case "calls": {
        const query = chart.queries?.[key] as AnyQuery;
        checked = this.checkedInput(refOfDefinition(this.spec, query), query.input, node?.calls?.[key]?.input, args);
        break;
      }
      case "sends": {
        const command = chart.commands[key] as AnyCommand;
        checked = this.checkedInput(refOfDefinition(this.spec, command), command.input, node?.sends?.[key]?.input, () =>
          this.args(scope, records, access, { createKey }),
        );
        break;
      }
      default: {
        const screen = chart.screens?.[key] as unknown as ChartSpec;
        checked = this.checkedInput(
          refOfDefinition(this.spec, screen),
          screen.input ?? {},
          node?.opens?.[key]?.input,
          args,
        );
      }
    }
    return checked instanceof Failed ? checked : { ...checked, created };
  }

  /** Checks the held values of a state, whose holds read the base arguments. */
  holds(scope: Scope, records: RecordSource, access: Access): undefined | Failed {
    const { named, ref } = this.chartOf(scope.machine);
    const state = this.stateOf(scope);
    const holds = named.definition.holds?.[state];
    if (holds === undefined) return undefined;
    const base = this.baseArgs(scope, records, access);
    for (const name of Object.keys(holds)) {
      const value = heldValue(ref, named.definition, state, name, base);
      if (value instanceof Failed) return value;
    }
    return undefined;
  }

  deadlines(machine: string, state: string): readonly (readonly [string, DeadlineTime])[] {
    const after = this.node(machine, state)?.after;
    if (after === undefined) return [];
    // Unlike Duration.total, Instant.add rejects date units and gives whole milliseconds, as Lean's Time is.
    const start = Temporal.Instant.fromEpochMilliseconds(0);
    return Object.entries(after).map(([name, d]) => [
      name,
      d.at === undefined ? { kind: "delay", ms: start.add(d.delay ?? {}).epochMilliseconds } : { kind: "atExpression" },
    ]);
  }

  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access): Temporal.Instant | Failed {
    const at = this.node(scope.machine, this.stateOf(scope))?.after?.[name]?.at as (args: unknown) => unknown;
    return attempt(() => at(this.args(scope, records, access)) as Temporal.Instant);
  }

  /** Returns the offers of the state `scope.state`, or of the chart itself when it is null. */
  offers(
    scope: Scope,
    records: RecordSource,
    control: string,
    access: Access,
  ): readonly { readonly value: Fields; readonly encoded: unknown }[] | Failed {
    const { named, ref } = this.chartOf(scope.machine);
    const f =
      scope.state === null
        ? named.definition.offers?.[control]
        : this.node(scope.machine, scope.state)?.offers?.[control];
    const given = attempt(() => f?.(this.args(scope, records, access) as never) ?? []);
    if (given instanceof Failed) return given;
    const payloads = valuesOf(given) ?? (given as readonly unknown[]);
    const row = strictObjectOf(named.definition.controls?.[control]?.payload ?? {});
    const checked: { readonly value: Fields; readonly encoded: unknown }[] = [];
    for (const o of payloads) {
      const payload = matching({ kind: "control", screen: ref, control }, row, o as Fields);
      if (payload instanceof Failed) return payload;
      checked.push(payload);
    }
    return checked;
  }

  showInput(
    scope: Scope,
    records: RecordSource,
    { key }: { readonly keyword: string; readonly key: string },
    access: Access,
  ): { readonly value: Fields; readonly encoded: unknown } | Failed {
    const query = this.chartOf(scope.machine).named.definition.queries?.[key] as AnyQuery;
    const f = this.node(scope.machine, this.stateOf(scope))?.shows?.[key]?.input;
    return this.checkedInput(refOfDefinition(this.spec, query), query.input, f, () =>
      this.args(scope, records, access),
    );
  }

  items(
    scope: Scope,
    records: RecordSource,
    access: Access,
  ): readonly { readonly key: unknown; readonly encoded: unknown; readonly encodedKey: string }[] | Failed {
    const map = this.stateOf(scope);
    const node = this.node(scope.machine, map);
    const given = attempt(() => node?.items?.(this.args(scope, records, access) as never) ?? []);
    if (given instanceof Failed) return given;
    const chart = this.chartOf(scope.machine).ref;
    const keys = matching({ kind: "mapKey", chart, map }, bag(objectOf(node?.key ?? {})), given);
    if (keys instanceof Failed) return keys;
    const encoded = keys.encoded as unknown[];
    return (valuesOf(keys.value) ?? []).map((key, i) => ({
      key,
      encoded: encoded[i],
      encodedKey: canonicalJson(encoded[i]),
    }));
  }

  /** Returns the defaults of the map state's copy context, which load checks against the schema. */
  copyContext(machine: string, map: string): Fields {
    const shape = this.node(machine, map)?.context ?? {};
    return bagged(objectOf(shape), defaultRow(shape)) as Fields;
  }

  /** Returns the defaults of a single entity's fields, which load checks against the schema. */
  singleRecord(entity: string): Row {
    const shape = this.entity(entity).fields as Shape;
    const value = defaultRow(shape);
    return { value: bagged(objectOf(shape), value) as Fields, encoded: encode(shape, value) as Fields };
  }

  copyKey(machine: string, map: string, payload: unknown): string | null | undefined | Failed {
    const shape = this.node(machine, map)?.key ?? {};
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
    const { named, ref } = this.chartOf(scope.machine);
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
