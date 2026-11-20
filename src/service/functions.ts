import { keyOrderIssue, sortCollections } from "../data/collections.ts";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Ensured } from "../data/ensured.generated.ts";
import type { Fault } from "../data/fault.generated.ts";
import { expectFound } from "../data/internalError.ts";
import type { Activity } from "../data/step.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.generated.ts";
import type { Fields, Json } from "../data/values.ts";
import { type Located, type ViolationError, withExtra, zodError } from "../data/violation.ts";
import { emitsOf } from "../spec/structure.ts";
import { ref, type Schema, type Service, schemaOf, schemaOwner } from "./basic.ts";
import { chartOf, type InstanceId, mapOf, ownerId } from "./instance.ts";
import type { Emit } from "./message.ts";
import type { RecordSource } from "./records.ts";

/**
 * The reason that a Functions question has no answer: its author code threw (with `schema`, inside that schema's
 * refinement or codec), a value does not match `schema`, an expression read a `held` name that its state does not
 * have, or it called `only()` on a bag with more than one element.
 */
export type Issue =
  | { readonly kind: "thrown"; readonly schema?: Schema }
  | { readonly kind: "schema"; readonly schema: Schema }
  | { readonly kind: "unheld"; readonly held: string }
  | { readonly kind: "notOnly" };

/** A question's Issue, with what only TS reports: the thrown value or the Zod issues. */
export class Failed {
  readonly issue: Issue;
  readonly error: ViolationError | undefined;

  constructor(issue: Issue, error?: ViolationError) {
    this.issue = issue;
    this.error = error;
  }
}

/**
 * Returns the fault that `failed` means at a site whose own author code belongs to `owner`, with the error that only TS
 * reports. A throw names `owner`, or the owner of the schema whose refinement or codec threw. An unheld read, a call
 * of `only()` on more than one element, and a held value that fails its schema, name `owner`; a value that fails any
 * other schema is the site's `mismatch`, an exception where the site checks no schema.
 */
export function issueViolation(
  owner: DefinitionRef,
  { issue, error }: Failed,
  mismatch: (schema: Schema) => Fault = () => ({ kind: "Fault.exception", definition: owner, data: {} }),
): Fault & Located {
  switch (issue.kind) {
    case "thrown": {
      const definition = issue.schema === undefined ? owner : schemaOwner(issue.schema);
      return withExtra({ kind: "Fault.exception", definition, data: {} }, { error });
    }
    case "unheld":
      return { kind: "Fault.unheld", definition: owner, data: { held: issue.held } };
    case "notOnly":
      return { kind: "Fault.notOnly", definition: owner, data: {} };
    case "schema": {
      const { schema } = issue;
      const fault: Fault =
        schema.kind === "held"
          ? { kind: "Fault.heldSchema", definition: owner, data: { state: schema.state } }
          : mismatch(schema);
      return withExtra(fault, { error });
    }
  }
}

/** Lean's Service.sorted: an encoded answer with its collections sorted by the structure's schema. */
const sorted = (st: Service, schema: Schema, json: Json): Json => sortCollections(schemaOf(st, schema), json);

/** Lean's Functions.parseSorted: a value that spec code made, sorted and then parsed. */
export const parseSorted = (st: Service, fs: Functions, schema: Schema, json: Json): Checked | Failed =>
  fs.parse(schema, sorted(st, schema, json));

/** Lean's lists: whether the command `command` lists the event of `e` in its emits. */
export function lists(st: Service, command: string, e: { readonly event: DefinitionRef }): boolean {
  return emitsOf(st.structure, ref(st, command)).some((l) => sameRef(l, e.event));
}

/** Lean's Functions.checked: a value that spec code made, sorted and parsed, or a schema Issue. */
function checked(st: Service, fs: Functions, schema: Schema, json: Json): Json | Failed {
  const parsed = parseSorted(st, fs, schema, json);
  if (parsed instanceof Failed) return parsed;
  return "error" in parsed ? new Failed({ kind: "schema", schema }, parsed.error) : (parsed.encoded as Json);
}

/** Lean's mapChecked: each of `xs` through `f`, in order, or the first Failed. */
function mapChecked<A, B>(xs: readonly A[], f: (x: A) => B | Failed): B[] | Failed {
  const ys: B[] = [];
  for (const x of xs) {
    const y = f(x);
    if (y instanceof Failed) return y;
    ys.push(y);
  }
  return ys;
}

/** Lean's Functions.sorting. */
export function sorting(st: Service, fs: Functions): Functions {
  const sortedInput = <T extends { readonly input: Json }>(schema: Schema, answer: T | Failed): T | Failed =>
    answer instanceof Failed ? answer : { ...answer, input: sorted(st, schema, answer.input) };
  return {
    parse: (...a) => fs.parse(...a),
    unordered: (...a) => fs.unordered(...a),
    decode: (...a) => fs.decode(...a),
    binding: (...a) => fs.binding(...a),
    requirement: (...a) => fs.requirement(...a),
    inputRequirement: (...a) => fs.inputRequirement(...a),
    decide: (name, input, records, now) => {
      const groups = fs.decide(name, input, records, now);
      if (groups instanceof Failed) return groups;
      return mapChecked(groups, (g) =>
        mapChecked(g, (e) => {
          if (!lists(st, name, e)) return e;
          const payload = checked(st, fs, { kind: "payload", event: e.event }, e.payload);
          return payload instanceof Failed ? payload : { ...e, payload };
        }),
      );
    },
    ensures: (...a) => fs.ensures(...a),
    queryEnsures: (...a) => fs.queryEnsures(...a),
    resultEnsures: (...a) => fs.resultEnsures(...a),
    invariant: (...a) => fs.invariant(...a),
    serviceInvariant: (...a) => fs.serviceInvariant(...a),
    chartInvariant: (...a) => fs.chartInvariant(...a),
    resolve: (name, input, records, now) => {
      const output = fs.resolve(name, input, records, now);
      return output instanceof Failed ? output : checked(st, fs, { kind: "output", definition: ref(st, name) }, output);
    },
    automationBinding: (...a) => fs.automationBinding(...a),
    automationGuard: (...a) => fs.automationGuard(...a),
    react: (name, payload, records, now, keys) => {
      const a = expectFound(
        `automation ${name}`,
        st.automations.find((x) => x.name === name),
      );
      return sortedInput({ kind: "input", definition: a.sends.target }, fs.react(name, payload, records, now, keys));
    },
    comparable: (...a) => fs.comparable(...a),
    initialContext: (machine, input) => {
      const context = fs.initialContext(machine, input);
      return context instanceof Failed ? context : sorted(st, { kind: "context", chart: ref(st, machine) }, context);
    },
    guard: (...a) => fs.guard(...a),
    assign: (scope, records, assignment, extra, keys, access) => {
      const answer = fs.assign(scope, records, assignment, extra, keys, access);
      if (answer instanceof Failed) return answer;
      const chart = ref(st, chartOf(scope.id));
      const context = checked(st, fs, { kind: "context", chart }, answer.context);
      if (context instanceof Failed || answer.copyContext === undefined)
        return context instanceof Failed ? context : { ...answer, context };
      const map = expectFound("the map state of a copy", mapOf(scope.id));
      const copyContext = checked(st, fs, { kind: "mapContext", chart, map }, answer.copyContext);
      return copyContext instanceof Failed ? copyContext : { ...answer, context, copyContext };
    },
    input: (scope, records, activity, keys, access) =>
      sortedInput({ kind: "input", definition: activity.target }, fs.input(scope, records, activity, keys, access)),
    held: (scope, records, state, edge, extra, access) => {
      const held = fs.held(scope, records, state, edge, extra, access);
      return held instanceof Failed
        ? held
        : checked(st, fs, { kind: "held", chart: ref(st, chartOf(scope.id)), state }, held);
    },
    deadlineAt: (...a) => fs.deadlineAt(...a),
    offers: (scope, records, control, access) => {
      const payloads = fs.offers(scope, records, control, access);
      const schema = { kind: "control", screen: ref(st, chartOf(scope.id)), control } as const;
      return payloads instanceof Failed ? payloads : mapChecked(payloads, (p) => checked(st, fs, schema, p));
    },
    showInput: (scope, records, activity, access) => {
      const input = fs.showInput(scope, records, activity, access);
      return input instanceof Failed ? input : sorted(st, { kind: "input", definition: activity.target }, input);
    },
    items: (scope, records, access) => {
      const keys = fs.items(scope, records, access);
      if (keys instanceof Failed) return keys;
      const map = expectFound("the map state of an items question", scope.state ?? undefined);
      const schema = { kind: "mapKey", chart: ref(st, chartOf(scope.id)), map } as const;
      return mapChecked(keys, (k) => checked(st, fs, schema, k));
    },
    defaults: (schema) => {
      const row = fs.defaults(schema);
      return row instanceof Failed ? row : sorted(st, schema, row);
    },
    close: (scope, records, access) => {
      const output = fs.close(scope, records, access);
      const schema = { kind: "output", definition: ref(st, chartOf(scope.id)) } as const;
      return output instanceof Failed ? output : checked(st, fs, schema, output);
    },
    closeEnsures: (...a) => fs.closeEnsures(...a),
  };
}

/** Lean's Functions.parseOutside, with the out-of-order element as the Zod issue that only TS reports. */
export function parseOutside(st: Service, fs: Functions, schema: Schema, value: unknown): Checked | Failed {
  const parsed = fs.parse(schema, value);
  if (parsed instanceof Failed || "error" in parsed) return parsed;
  const issue = keyOrderIssue(schemaOf(st, schema), parsed.encoded as Json);
  return issue === undefined ? parsed : { error: zodError([issue]) };
}

/** Lean's firstFalse: the first of `names` that `test` finds false, in order. */
export function firstFalse<N, R extends boolean | Failed>(
  test: (name: N) => R,
  names: readonly N[],
): N | undefined | Exclude<R, boolean> {
  for (const name of names) {
    const holds: boolean | Failed = test(name);
    if (holds instanceof Failed) return holds as Exclude<R, boolean>;
    if (!holds) return name;
  }
  return undefined;
}

/** Lean's Ensured.passes. */
export const passes = (ensured: Ensured): boolean => ensured !== "fails";

/** The scope of a copy: its decoded item key and its own context. */
export interface CopyScope {
  readonly key: unknown;
  readonly context: Fields;
}

/**
 * The values passed to machine and screen expressions. `id` is the evaluating instance or copy. `state` is the state
 * that declares the expression (null for the chart's own `on`). `held` holds the parameters of that state for its
 * current visit (empty when it has none). `active` holds the active state names (a copy's and its owner's), looked up
 * when an expression reads them. `context` is the instance's (the owner's for a copy). `shown` holds the answer's
 * output for each shows slot (null if none). `input` is the screen's input.
 */
export interface Scope {
  readonly id: InstanceId;
  readonly state: string | null;
  readonly context: Fields;
  readonly copy: CopyScope | undefined;
  readonly active: Pick<ReadonlySet<string>, "has">;
  readonly shown: ReadonlyMap<string, unknown>;
  readonly input: Fields;
  readonly held: Fields;
  readonly now: Temporal.Instant;
}

/**
 * The holder of a value that an expression read or assigned: the owner (the instance if it is not a copy) or the copy.
 */
export type Holder = "owner" | "copy";

export function holderId(scope: Scope, holder: Holder): InstanceId {
  return holder === "copy" ? scope.id : ownerId(scope.id);
}

/** What the expressions of a Scope question read and assign, told as they do. Only TS has it. */
export interface Access {
  context(holder: Holder, field: string): void;
  active(holder: Holder, state: string): void;
  assigned(holder: Holder, field: string): void;
  shown(slot: string): void;
  now(): void;
}

export type Assignment =
  | { readonly kind: "transition"; readonly transition: TransitionRef }
  | { readonly kind: "entry" | "exit"; readonly state: string };

/**
 * Lean's Edge: the edge that enters a state with parameters and fills them with its `with`, a transition that targets
 * the state or the initial edge of its parent.
 */
export type Edge =
  | { readonly kind: "transition"; readonly transition: TransitionRef }
  | { readonly kind: "initial"; readonly parent: string };

/** What createKey returns next for an entity: `<entity>-<n>` for its `n`-th createKey value, after `count` so far. */
export interface NextKeys {
  readonly count: number;
}

/** Lean's Keys: what createKey returns next per entity, qualified by the running service `owner` of a simulation. */
export interface Keys {
  readonly owner?: string;
  readonly next: readonly (readonly [string, NextKeys])[];
}

/**
 * Lean's givenKeys: the createKey values, each with its entity, that createKey gives to calls for the entities
 * `created`, in call order, when `keys` holds what it returns next.
 */
export function givenKeys(keys: Keys, created: readonly string[]): [string, string][] {
  const next = new Map(keys.next);
  return created.map((e, i) => {
    const k = next.get(e) ?? { count: 0 };
    const before = created.slice(0, i).filter((c) => c === e).length;
    const counted = `${e}-${k.count + before + 1}`;
    return [e, keys.owner === undefined ? counted : `${keys.owner}/${counted}`];
  });
}

/** A checked value, decoded for spec functions and encoded as written, or why it does not match its schema. */
export type Checked = { readonly value: Fields; readonly encoded: unknown } | { readonly error: ViolationError };

/**
 * Lean's Functions, the TS side of the questions in the same order. An own definition is named by its name, and a
 * definition that may belong to another service by its ref; values are decoded. Each question that runs author code
 * answers its value or the Failed that stopped it.
 */
export interface Functions {
  parse(schema: Schema, value: unknown): Checked | Failed;
  /**
   * Returns a value from outside or of a trace line as a simulation compares it: canonical, with every bag and the
   * sortedBy elements with equal keys in canonical order.
   */
  unordered(schema: Schema, value: unknown): unknown;
  /** Returns a value of `schema` from its checked encoding, as spec code receives it. */
  decode(schema: Schema, value: Json): Fields;
  binding(
    command: string,
    binding: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed;
  requirement(
    command: string,
    condition: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed;
  inputRequirement(target: DefinitionRef, condition: string, input: Fields): boolean | Failed;
  /**
   * Lean's decide: the events in groups, the groups in order and the events of one group in none. Each payload of an
   * event that the command lists is encoded by its event's schema in the order it was built; any other payload is null.
   */
  decide(
    command: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): readonly (readonly Decided[])[] | Failed;
  /**
   * Returns the first failing ensures. Binds read `before`, the records before the event write; ensures read `after`.
   */
  ensures(
    command: string,
    input: Fields,
    before: RecordSource,
    after: RecordSource,
    now: Temporal.Instant,
  ): string | undefined | Failed;
  queryEnsures(query: string, input: Fields, output: Fields, records: RecordSource): string | undefined | Failed;
  /** Returns what the ensures `condition` of `target` gives on a request's results. */
  resultEnsures(
    target: DefinitionRef,
    condition: string,
    input: Fields,
    output: unknown,
    events: readonly Emit[],
  ): Ensured | Failed;
  invariant(entity: string, record: Fields): string | undefined | Failed;
  serviceInvariant(records: RecordSource): string | undefined | Failed;
  chartInvariant(scope: Scope, records: RecordSource, access: Access): string | undefined | Failed;
  /** Lean's resolve: the output, encoded by its schema in the order it was built. */
  resolve(query: string, input: Fields, records: RecordSource, now: Temporal.Instant): Json | Failed;
  automationBinding(
    automation: string,
    binding: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed;
  automationGuard(
    automation: string,
    condition: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): boolean | Failed;
  /**
   * Returns the input of the automation's command as the sender writes it, once its guard holds. `keys` holds what
   * createKey returns next per entity (an entity that `keys` lacks has none so far), and `created` holds the entities
   * that react called createKey for, in call order.
   */
  react(
    automation: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
    keys: Keys,
  ): { readonly input: Json; readonly created: readonly string[] } | Failed;
  /**
   * Returns a query answer as verify compares it, ignoring bag and set order and the order of sortedBy elements with
   * equal keys.
   */
  comparable(query: string, answer: Answer): unknown;
  /** Lean's initialContext: what the initialContext of `machine` computes from `input`, encoded, or {} without one. */
  initialContext(machine: string, input: Fields): Json | Failed;
  /**
   * Evaluates one guard condition. `extra` is what caused the transition (its payload, output, or rejection), or {} for
   * none.
   */
  guard(
    scope: Scope,
    records: RecordSource,
    transition: TransitionRef,
    condition: string,
    extra: Fields,
    access: Access,
  ): boolean | Failed;
  /**
   * Lean's assign: the context after the assign, unchanged where there is none, checked and encoded. For a copy, copy
   * context fields go to `copyContext` and the rest to `context`. `keys` and `created` are as in react.
   */
  assign(
    scope: Scope,
    records: RecordSource,
    assignment: Assignment,
    extra: Fields,
    keys: Keys,
    access: Access,
  ): { readonly context: Json; readonly copyContext: Json | undefined; readonly created: readonly string[] } | Failed;
  /**
   * Returns the input of the request that a state sends, or of the screen it opens, as the sender writes it. `keys`
   * and `created` are as in react.
   */
  input(
    scope: Scope,
    records: RecordSource,
    activity: Activity,
    keys: Keys,
    access: Access,
  ): { readonly input: Json; readonly created: readonly string[] } | Failed;
  /**
   * Returns the parameters of `state`, which `edge` enters and its `with` computes, checked against the held schema of
   * `state`. A transition's `with` reads what its assign reads.
   */
  held(scope: Scope, records: RecordSource, state: string, edge: Edge, extra: Fields, access: Access): Json | Failed;
  /** Lean's deadlineAt, with undefined for none. */
  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access): string | undefined | Failed;
  /** Lean's offers: the payloads, checked and encoded in the order they were built. */
  offers(scope: Scope, records: RecordSource, control: string, access: Access): readonly Json[] | Failed;
  /** Returns the query input of a shows slot as the sender writes it. */
  showInput(scope: Scope, records: RecordSource, activity: Activity, access: Access): Json | Failed;
  /** Lean's items: each item key, checked and encoded in the order they were built. The map state takes them as a set. */
  items(scope: Scope, records: RecordSource, access: Access): readonly Json[] | Failed;
  /** Lean's defaults: the default value of each field of `schema` that declares one, encoded in the order it was built. */
  defaults(schema: Schema): Json | Failed;
  /** Lean's close: the output of a screen that closes in a final state, checked and encoded in the order it was built. */
  close(scope: Scope, records: RecordSource, access: Access): Json | Failed;
  /** Lean's closeEnsures: the first failing ensures of `screen`, which closed with `input` and the sorted `output`. */
  closeEnsures(screen: string, input: Fields, output: Fields): string | undefined | Failed;
}

/** An event that decide returns, with its payload encoded. */
export interface Decided {
  readonly event: DefinitionRef;
  readonly payload: Json;
}
