import type { z } from "zod";
import type { RejectionKind } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import { type GivenDefiner, givenDefiner, type ScenarioDefiner, scenarioDefiner } from "../scenario/define.ts";
import { type BoundsDefiner, boundsDefiner } from "./bounds.ts";
import type { Conditions, Named, Now, Present } from "./conditions.ts";
import type { ConstantsGroup } from "./constants.ts";
import type { Contract, RecordsData } from "./contract.ts";
import type {
  AnyCommand,
  AnyEvent,
  AnyQuery,
  Automation,
  Binds,
  Command,
  CreateKey,
  Emit,
  Emits,
  FieldsEvent,
  Owned,
  Payload,
  Query,
  ServiceDefinition,
} from "./definition.ts";
import type { Entities, MadeRow, Records, Row } from "./entity.ts";
import {
  type CreateEventDefiner,
  type DeleteEventDefiner,
  type EventDefiner,
  eventDefiners,
  type UpdateEventDefiner,
} from "./event.ts";
import { type MachineDefiner, machineDefiner } from "./machine.ts";
import { type ScreenDefiner, screenDefiner } from "./screen.ts";
import type { ErrorIf, IsUnion } from "./tree.ts";

type Input<I extends Shape> = Row<I>;
type Bound<B> = { readonly [K in keyof B]: NonNullable<B[K]> };

interface Definers<Es extends Entities, N extends string> {
  /** Defines a command: a request to change records. */
  command<
    const I extends Shape = Record<never, never>,
    const Ev extends AnyEvent = never,
    const B = Record<never, never>,
    const Rq extends string = never,
    const En extends string = never,
    const Bn extends string = never,
  >(definition: {
    input?: I;
    /** The events that the command emits, of this service only (`Illegal.foreignEvent`). */
    emits: readonly Ev[];
    /** The values that `requires`, `decide`, and `ensures` read as `bound`. */
    binds?: Binds<{ input: Input<I>; records: Records<Es> } & Now, B> & Present<Bn>;
    /**
     * Checked after `binds`, each in written order. The first that fails names the rejection reason. No key of either
     * may be an array index such as `1`, which JavaScript lists before the other keys (`Illegal.indexReason`).
     */
    requires?: Named<Rq, { input: Input<I>; records: Records<Es>; bound: Bound<B> } & Now>;
    /** `records` holds the records after the events. `bound` holds the values from before them. */
    ensures?: Named<En, { input: Input<I>; records: Records<Es>; bound: Bound<B> }>;
  }): CommandSetup<I, Ev, B, Rq, Es, N>;
  /** Defines a query: a request to read records. */
  query<
    const I extends Shape = Record<never, never>,
    const O extends Shape = Shape,
    const Rq extends string = never,
    const En extends string = never,
  >(definition: {
    input?: I;
    /** A lookup that can miss uses a nullable field. */
    output: O;
    /** Checked as a command's `requires`. */
    requires?: Named<Rq, { input: Input<I> }>;
    ensures?: Named<En, { input: Input<I>; output: Row<O>; records: Records<Es> }>;
  }): QuerySetup<I, O, Rq, Es, N>;
  /**
   * Defines an automation: on each received event it sends one command and keeps no context. Waiting for an answer or a
   * deadline, or reacting to a rejection, needs a machine (`NonCanonical.statelessMachine`).
   */
  automation<
    const Rs extends Readonly<Record<string, AnyEvent>>,
    const Cs extends Readonly<Record<string, AnyCommand>>,
  >(setup: {
    /** The received event: an event of this service, or of another service through its contract. */
    receives: Rs & OneKey<Rs>;
    commands: Cs & OneKey<Cs>;
  }): AutomationSetup<Rs[keyof Rs], Cs, Es>;
  /**
   * Defines a statechart that waits for events, answers, and deadlines. It reads other services' values only from
   * received payloads and query outputs, never from another machine's state.
   */
  machine: MachineDefiner<Es>;
  /** Defines a machine driven by user operations that shows query answers. */
  screen: ScreenDefiner<Es>;
  /** Defines an event that creates a record. The payload is the whole record. */
  createEvent: CreateEventDefiner<Es, N>;
  /**
   * Defines an event that updates the `writes` fields. The payload is the key (none for a single entity) and those
   * fields.
   */
  updateEvent: UpdateEventDefiner<Es, N>;
  /** Defines an event that deletes a record. The payload is the key. */
  deleteEvent: DeleteEventDefiner<Es, N>;
  /** Defines an event that changes no record, with the fields of `payload`. */
  event: EventDefiner<N>;
  /** Defines the contract of the service, whose spec tazuna runs. */
  contract: ContractDefiner<RecordsData<Es>, "spec", N>;
  /** Defines a scenario of the service (ScenarioDefiner). */
  scenario: ScenarioDefiner<RecordsData<Es>, N>;
  /** Defines a Given that scenarios share (GivenDefiner). */
  given: GivenDefiner<RecordsData<Es>, N>;
  /** Defines the bounds of the states that `prove` checks the service's invariants in, at most one per service. */
  bounds: BoundsDefiner<Es>;
  /**
   * Returns `condition` as is, typed with the service's records, so that guards and `requires` of the service share
   * one function.
   */
  condition(
    condition: (args: { records: Records<Es> } & Now) => boolean,
  ): (args: { records: Records<Es> } & Now) => boolean;
}

interface CommandSetup<
  I extends Shape,
  Ev extends AnyEvent,
  B,
  Rq extends string,
  Es extends Entities,
  N extends string,
> {
  decide(
    decide: (args: { input: Input<I>; records: Records<Es>; bound: Bound<B> } & Now) => Emits<Ev>,
  ): Command<I, Ev, keyof B & string, Rq, undefined, undefined> & Owned<N>;
}

interface QuerySetup<I extends Shape, O extends Shape, Rq extends string, Es extends Entities, N extends string> {
  resolve(
    resolve: (args: { input: Input<I>; records: Records<Es> } & Now) => MadeRow<O>,
  ): Query<I, O, Rq, undefined> & Owned<N>;
}

type AutomationArgs<Ev extends AnyEvent, Es extends Entities> = Now & {
  readonly payload: Payload<Ev>;
  readonly records: Records<Es>;
};

type OneKey<T> = [keyof T] extends [never]
  ? { "~one": never }
  : true extends IsUnion<keyof T>
    ? { "~one": never }
    : unknown;

/** `send` has `input` exactly when its command has input fields. */
type SendInput<C, Args> =
  C extends Command<infer I, AnyEvent>
    ? keyof I extends never
      ? { input?: never }
      : { input: (args: Args) => MadeRow<I> }
    : never;

interface AutomationSetup<Ev extends AnyEvent, Cs extends Readonly<Record<string, AnyCommand>>, Es extends Entities> {
  /** Sends the command when `guard` holds, or always without `guard`. */
  send<const B = Record<never, never>, const Bn extends string = never, const G extends string = never>(
    definition: {
      /** The values that `guard` and `input` read as `bound`. */
      binds?: Binds<AutomationArgs<Ev, Es>, B> & Present<Bn>;
      /** A condition that checks the same as one of the command's `requires` calls the same `condition`. */
      guard?: Named<G, AutomationArgs<Ev, Es> & { bound: Bound<B> }>;
      /**
       * Ignores an unavailable rejection, the only kind that is not a fault of the automation
       * (`Fault.rejectedAutomationCommand`). Written exactly when one can arrive: the command is of another service and
       * may reject with unavailable (`NonCanonical.missingOnRejected`, `NonCanonical.unreachableOnRejected`). The
       * precedent is Swift's `try?`.
       */
      onRejected?: readonly [];
    } & SendInput<Cs[keyof Cs], AutomationArgs<Ev, Es> & { bound: Bound<B> } & CreateKey>,
  ): Automation;
}

type Emitted<Ev> = Ev extends AnyEvent ? Emit<Ev> : never;
type OutputArgs<O extends Shape> = [keyof O] extends [never] ? unknown : { output: Row<O> };

interface ExternalDefiners<N extends string> {
  /** Defines a command whose answers and `emits` events the external implementation makes. */
  command<
    const I extends Shape = Record<never, never>,
    const O extends Shape = Record<never, never>,
    const Ev extends AnyEvent = never,
    const Rq extends string = never,
    const En extends string = never,
    const Rj extends readonly RejectionKind[] = never,
  >(definition: {
    input?: I;
    output?: O;
    emits: readonly Ev[];
    /**
     * The kinds that the external implementation may reject with. `test` explores only these, and `verify` reports
     * others.
     */
    rejects: Rj;
    /** The external implementation rejects with `requires` when one fails. */
    requires?: Named<Rq, { input: Input<I> }>;
    /** `events` are the events that have arrived as results of the request (resultOf). */
    ensures?: Named<En, { input: Input<I>; events: readonly Emitted<Ev>[] } & OutputArgs<O>>;
  }): Command<I, Ev, never, Rq, [keyof O] extends [never] ? undefined : O, Rj> & Owned<N>;
  /** Defines a query whose answers the external implementation makes. */
  query<
    const I extends Shape = Record<never, never>,
    const O extends Shape = Shape,
    const Rq extends string = never,
    const En extends string = never,
    const Rj extends readonly RejectionKind[] = never,
  >(definition: {
    input?: I;
    output: O;
    /**
     * The kinds that the external implementation may reject with. `test` explores only these, and `verify` reports
     * others.
     */
    rejects: Rj;
    /** The external implementation rejects with `requires` when one fails. */
    requires?: Named<Rq, { input: Input<I> }>;
    ensures?: Named<En, { input: Input<I>; output: Row<O> }>;
  }): Query<I, O, Rq, Rj> & Owned<N>;
  /** Defines an event that the external implementation emits, with the fields of `payload`. */
  event: EventDefiner<N>;
  /** Defines the contract of the service, which tazuna takes as contract only. */
  contract: ContractDefiner<Record<never, never>, "external", N>;
}

/**
 * The characters that tazuna's generated names put between parts (`<service>.<name>`, `<service>/<Entity>-<n>`,
 * `<sender>/<id>`, `<name>#<n>`), which a service or scenario name does not contain
 * (`Malformed.reservedNameCharacter`).
 */
export const reservedNameCharacters = [".", "/", "#"] as const;
type ReservedIn<N extends string> = ErrorIf<
  "reservedNameCharacter",
  N & `${string}${(typeof reservedNameCharacters)[number]}${string}`
>;

/**
 * Defines an external service (for example an OS calendar): the spec states only `requires` and `ensures` of its
 * answers and events, never how they are made.
 */
export function externalService<const N extends string>(
  definition: {
    /** The service's name, which names it in contracts, scenarios, constants and traces. */
    name: N;
    description: string;
  } & ReservedIn<N>,
): ExternalDefiners<N> {
  const owner = serviceDefinition({ name: definition.name, description: definition.description, entities: {} }, true);
  const command = (d: CommandOptions) => commandOf(owner, d, undefined);
  const query = (d: QueryOptions) => queryOf(owner, d, undefined);
  const { event } = eventDefiners(owner);
  const contract = contractDefiner(owner);
  register(owner, [command, query, event, contract]);
  return { command, query, event, contract } as unknown as ExternalDefiners<N>;
}

/** Defines a service that owns `entities` and returns its definers. */
export function service<
  const N extends string,
  const Es extends Entities = Record<never, never>,
  const Iv extends string = never,
>(
  definition: {
    /** The service's name, which names it in contracts, scenarios, constants and traces. */
    name: N;
    description: string;
    entities?: Es;
    /** The conditions over all records (`Fault.failedServiceInvariant`). */
    invariants?: Named<Iv, { records: Records<Es> } & Now>;
  } & ReservedIn<N>,
): Definers<Es, N> {
  return definers(
    serviceDefinition(
      definition as { name: string; description: string; entities?: Entities; invariants?: Conditions<never> },
      false,
    ),
  ) as unknown as Definers<Es, N>;
}

type CommandOptions = {
  input?: Shape;
  output?: Shape;
  emits: readonly AnyEvent[];
  rejects?: readonly RejectionKind[];
  binds?: Binds<never>;
  requires?: Conditions<never>;
  ensures?: Conditions<never>;
};
type QueryOptions = {
  input?: Shape;
  output: Shape;
  rejects?: readonly RejectionKind[];
  requires?: Conditions<never>;
  ensures?: Conditions<never>;
};

function serviceDefinition(
  definition: { name: string; description: string; entities?: Entities; invariants?: Conditions<never> },
  external: boolean,
): ServiceDefinition {
  return {
    kind: "service",
    name: definition.name,
    description: definition.description,
    entities: definition.entities ?? {},
    invariants: definition.invariants ?? {},
    external,
  };
}

const commandOf = (
  owner: ServiceDefinition,
  d: CommandOptions,
  decide: ((args: never) => Emits) | undefined,
): AnyCommand => ({
  kind: "command",
  service: owner,
  input: d.input ?? {},
  output: d.output,
  emits: d.emits,
  binds: d.binds ?? {},
  requires: d.requires ?? {},
  ensures: d.ensures ?? {},
  decide,
  rejects: d.rejects,
});

const queryOf = (
  owner: ServiceDefinition,
  d: QueryOptions,
  resolve: ((args: never) => unknown) | undefined,
): AnyQuery => ({
  kind: "query",
  service: owner,
  input: d.input ?? {},
  output: d.output,
  requires: d.requires ?? {},
  ensures: d.ensures ?? {},
  resolve,
  rejects: d.rejects,
});

function register(owner: ServiceDefinition, definers: readonly object[]): void {
  for (const definer of definers) definerOwners.set(definer, owner);
}

function definers(owner: ServiceDefinition): Definers<Entities, string> {
  const command = (d: CommandOptions) => ({
    decide: (decide: (args: never) => Emits) => commandOf(owner, d, decide),
  });
  const query = (d: QueryOptions) => ({ resolve: (resolve: (args: never) => unknown) => queryOf(owner, d, resolve) });
  const automation = (setup: {
    receives: Readonly<Record<string, AnyEvent>>;
    commands: Readonly<Record<string, AnyCommand>>;
  }) => ({
    send: (d: {
      binds?: Binds<never>;
      guard?: Conditions<never>;
      input?: (args: never) => unknown;
      onRejected?: readonly [];
    }): Automation => ({
      kind: "automation",
      service: owner,
      receives: setup.receives,
      commands: setup.commands,
      binds: d.binds ?? {},
      guard: d.guard ?? {},
      input: d.input,
      onRejected: d.onRejected,
    }),
  });
  const machine = machineDefiner(owner);
  const screen = screenDefiner(owner);
  const events = eventDefiners(owner);
  const contract = contractDefiner(owner);
  const scenario = scenarioDefiner(owner);
  const given = givenDefiner();
  const condition = <F>(f: F): F => f;
  const bounds = boundsDefiner(owner);
  register(owner, [
    command,
    query,
    automation,
    machine,
    screen,
    contract,
    scenario,
    given,
    condition,
    bounds,
    ...Object.values(events),
  ]);
  return {
    command,
    query,
    automation,
    machine,
    screen,
    contract,
    scenario,
    given,
    condition,
    bounds,
    ...events,
  } as unknown as Definers<Entities, string>;
}

type Member = FieldsEvent | AnyCommand | AnyQuery | z.ZodType | ConstantsGroup;

const contractOwners = new WeakMap<object, ServiceDefinition>();
const definerOwners = new WeakMap<object, ServiceDefinition>();

export function definerService(value: unknown): ServiceDefinition | undefined {
  return typeof value === "function" ? definerOwners.get(value) : undefined;
}

type Members<M> = { readonly [K in keyof M]: Member };

/**
 * Marks the members that other services may refer to (`Restricted.crossServiceImport`), possibly none.
 */
type ContractDefiner<R, K extends "spec" | "external", N extends string> = <const M extends Members<M>>(
  members: M,
) => Contract<M, R, K, N>;

const contractDefiner =
  (owner: ServiceDefinition) =>
  <M extends object>(members: M): M => {
    contractOwners.set(members, owner);
    return members;
  };

export const contractService = (value: unknown): ServiceDefinition | undefined =>
  typeof value === "object" && value !== null ? contractOwners.get(value) : undefined;

export function isContract(value: unknown): value is Readonly<Record<string, unknown>> {
  return typeof value === "object" && value !== null && contractOwners.has(value);
}
