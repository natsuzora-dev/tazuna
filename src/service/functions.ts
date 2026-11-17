import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Fault } from "../data/fault.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.ts";
import type { Fields } from "../data/values.ts";
import { type Located, type ProblemError, withExtra } from "../data/violation.ts";
import { type Schema, schemaOwner } from "./basic.ts";
import type { Emit } from "./message.ts";
import type { RecordSource, Row } from "./records.ts";

/**
 * The reason that a Functions question has no answer: its author code threw (with `schema`, inside that schema's
 * refinement or codec), a value does not match `schema`, an expression read a `held` name that no enclosing state
 * holds, or it called `only()` on a bag with more than one element.
 */
export type Issue =
  | { readonly kind: "thrown"; readonly schema?: Schema }
  | { readonly kind: "schema"; readonly schema: Schema }
  | { readonly kind: "unheld"; readonly held: string }
  | { readonly kind: "notOnly" };

/** A question's Issue, with what only TS reports: the thrown value or the Zod issues. */
export class Failed {
  readonly issue: Issue;
  readonly error: ProblemError | undefined;

  constructor(issue: Issue, error?: ProblemError) {
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
          ? { kind: "Fault.heldSchema", definition: owner, data: { held: schema.name, state: schema.state } }
          : mismatch(schema);
      return withExtra(fault, { error });
    }
  }
}

/** The scope of a copy; `map` is the copy's map state. */
export interface CopyScope {
  readonly map: string;
  readonly key: unknown;
  readonly context: Fields;
}

/**
 * The values passed to machine and screen expressions. `resource` is the evaluating instance or copy, and `owner` is
 * its owner (itself if it is not a copy). `state` is the state that declares the expression (null for the chart's own
 * `on`). `active` holds the active state names (a copy's and its owner's), looked up when an expression reads them.
 * `context` is the instance's (the owner's for a copy). `shown` holds the answer's output for each shows slot (null if
 * none). `input` is the screen's input.
 */
export interface Scope {
  readonly machine: string;
  readonly resource: string;
  readonly owner: string;
  readonly state: string | null;
  readonly context: Fields;
  readonly copy: CopyScope | undefined;
  readonly active: Pick<ReadonlySet<string>, "has">;
  readonly shown: ReadonlyMap<string, unknown>;
  readonly input: Fields;
  readonly now: Temporal.Instant;
}

/**
 * The holder of a value that an expression read or assigned: the owner (the instance if it is not a copy) or the copy.
 */
export type Holder = "owner" | "copy";

export function holderResource(scope: Scope, holder: Holder): string {
  return holder === "copy" ? scope.resource : scope.owner;
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

/** What createKey returns next for an entity: `<entity>-<n>` for its `n`-th createKey value, after `count` so far. */
export interface NextKeys {
  readonly count: number;
}

/** Lean's Keys: what createKey returns next per entity, qualified by the participant `owner` of a simulation. */
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

export type DeadlineTime = { readonly kind: "delay"; readonly ms: number } | { readonly kind: "atExpression" };

/** A checked value, decoded for spec functions and encoded as written, or why it does not match its schema. */
export type Checked = { readonly value: Fields; readonly encoded: unknown } | { readonly error: ProblemError };

/**
 * Lean's Functions, the TS side of the questions in the same order. Definitions are named by trace name as seen from
 * the service; values are decoded. Each question that runs author code answers its value or the Failed that stopped it.
 */
export interface Functions {
  parse(schema: Schema, value: unknown): Checked | Failed;
  canonical(schema: Schema, value: unknown): unknown;
  /**
   * Returns a value from outside or of a trace line as a simulation compares it: canonical, with every bag and the
   * sortedBy elements with equal keys in canonical order.
   */
  unordered(schema: Schema, value: unknown): unknown;
  normalize(schema: Schema, value: unknown): Checked | Failed;
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
  inputRequirement(target: string, condition: string, input: Fields): boolean | Failed;
  /** Returns the events in groups: the groups are in order, and the events of one group have none. */
  decide(
    command: string,
    input: Fields,
    records: RecordSource,
    now: Temporal.Instant,
  ): readonly (readonly Emit[])[] | Failed;
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
  resultEnsures(target: string, input: Fields, output: unknown, events: readonly Emit[]): string | undefined | Failed;
  invariant(entity: string, record: Fields): string | undefined | Failed;
  serviceInvariant(records: RecordSource): string | undefined | Failed;
  chartInvariant(scope: Scope, records: RecordSource, access: Access): string | undefined | Failed;
  resolve(query: string, input: Fields, records: RecordSource, now: Temporal.Instant): unknown;
  /**
   * Returns the input of the automation's command, undefined when a binds value is null or the guard fails. `keys`
   * holds what createKey returns next per entity (an entity that `keys` lacks has none so far), and `created` holds the
   * entities that react called createKey for, in call order.
   */
  react(
    automation: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
    keys: Keys,
  ): { readonly input?: unknown; readonly created: readonly string[] } | Failed;
  /**
   * Returns a query answer as verify compares it, ignoring bag and set order and the order of sortedBy elements with
   * equal keys.
   */
  comparable(query: string, answer: Answer): unknown;
  initialContext(machine: string, input: Fields): Fields | Failed;
  /** Evaluates a guard. `extra` is what caused the transition (its payload, output, or rejection), or {} for none. */
  guard(
    scope: Scope,
    records: RecordSource,
    transition: TransitionRef,
    extra: Fields,
    access: Access,
  ): boolean | Failed;
  /**
   * Returns the context after the assign, unchanged where there is none. For a copy, copy context fields go to
   * `copyContext` and the rest to `context`. `keys` and `created` are as in react.
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
    | Failed;
  /**
   * Returns the input of the request that a state sends, or of the screen it opens. `keys` and `created` are as in
   * react.
   */
  input(
    scope: Scope,
    records: RecordSource,
    activity: { readonly keyword: string; readonly key: string },
    keys: Keys,
    access: Access,
  ): { readonly value: Fields; readonly encoded: unknown; readonly created: readonly string[] } | Failed;
  holds(scope: Scope, records: RecordSource, access: Access): undefined | Failed;
  /** Returns the names of a state's `after` deadlines and how each time is set, in declaration order. */
  deadlines(machine: string, state: string): readonly (readonly [string, DeadlineTime])[];
  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access): Temporal.Instant | Failed;
  offers(
    scope: Scope,
    records: RecordSource,
    control: string,
    access: Access,
  ): readonly { readonly value: Fields; readonly encoded: unknown }[] | Failed;
  showInput(
    scope: Scope,
    records: RecordSource,
    activity: { readonly keyword: string; readonly key: string },
    access: Access,
  ): { readonly value: Fields; readonly encoded: unknown } | Failed;
  /** Returns each item key, encoded and as canonicalJson of the encoding. The map state takes them as a set. */
  items(
    scope: Scope,
    records: RecordSource,
    access: Access,
  ): readonly { readonly key: unknown; readonly encoded: unknown; readonly encodedKey: string }[] | Failed;
  copyContext(machine: string, map: string): Fields;
  /** Returns the initial record of a single entity, decoded and encoded. */
  singleRecord(entity: string): Row;
  /**
   * Returns the copy key of the payload: null when the payload's key fields fail the key schema, and undefined when the
   * payload has no key fields, in which case it reaches every copy.
   */
  copyKey(machine: string, map: string, payload: unknown): string | null | undefined | Failed;
  /** Returns the output of a screen that closes in a final state, and its first failing ensures. */
  close(
    scope: Scope,
    records: RecordSource,
    access: Access,
  ): { readonly output: Fields; readonly failed: string | undefined } | Failed;
}
