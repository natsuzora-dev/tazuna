import type { Delay } from "../data/datetime.ts";
import type { RejectionKind } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import type { Conditions, Named, SomeKey } from "./conditions.ts";
import type {
  AcceptedOutput,
  AnyCommand,
  AnyQuery,
  CreateKey,
  Events,
  InputOf,
  Machine,
  Now,
  Payload,
  QueryOutput,
  ServiceDefinition,
  TransitionSpec,
} from "./definition.ts";
import type { DefaultedShape, Entities, Records, Row } from "./entity.ts";
import {
  assemble,
  type CheckTree,
  type CopyContext,
  type CopyKey,
  type CopyNames,
  type ErrorIf,
  type Flat,
  type HeldIn,
  type KindOf,
  type MapOf,
  type OuterNames,
  type OutsideRegionOrMap,
  type RowsWritten,
  type SharedContextFields,
  type SomeKnownKey,
  type Table,
  type TableKeys,
  type Tree,
  type TreeErrors,
} from "./tree.ts";

export interface BaseArgs<Ctx, N extends string, D> extends Now {
  readonly context: Ctx;
  readonly records: D;
  /**
   * The states outside the region or map state that holds the expression, or no states when no region or map state
   * holds it.
   */
  readonly active: { readonly [S in N]: boolean };
}

type Assign<Ctx, A> = SomeKnownKey<Ctx> & { readonly [K in keyof Ctx]?: (args: A & CreateKey) => Ctx[K] };

type Transition<N extends string, Ctx, A> = {
  /**
   * The conditions of the transition. When a guard checks the same condition as a `requires` of a command that the
   * state sends: for another service's records, read that service's query answer (`shown` or a `calls` answer); for the
   * own service's records, call the function that the `requires` calls; for values that only the sender holds
   * (`context`, `payload`), write the same expression in the guard. An empty guard is NonCanonical.emptyGuard and not a
   * type error: TS rejects an empty object only through a type parameter inferred from its keys (SomeKey), and chart
   * infers only the written state keys.
   */
  readonly guard?: Conditions<A>;
  readonly assign?: Assign<Ctx, A>;
} & (
  | {
      readonly target: NoInfer<N>;
      /**
       * Whether the transition exits and re-enters its source state; written exactly when `target` is the state that
       * writes the transition or a descendant of that state (NonCanonical.missingReenter, NonCanonical.reenterOnRoot,
       * NonCanonical.reenterOutsideSource).
       */
      readonly reenter?: boolean;
    }
  | { readonly target?: never; readonly reenter?: never }
);
export type Transitions<N extends string, Ctx, A> = readonly Transition<N, Ctx, A>[];
type NoAt = { readonly at?: never };
type NoDelay = { readonly delay?: never };
/** A deadline. `at` does not read `now`, because a fixed length from now is a `delay`. */
type Deadline<N extends string, Ctx, A> = {
  readonly onFired: Transitions<N, Ctx, A>;
} & (({ readonly delay: Delay } & NoAt) | ({ readonly at: (args: Omit<A, "now">) => Temporal.Instant } & NoDelay));
export type Queries = Readonly<Record<string, AnyQuery>>;
export type Commands = Readonly<Record<string, AnyCommand>>;

export type KeyedTransitions<
  N extends string,
  Ctx,
  B,
  ArgsByKey extends Readonly<Record<string, object>>,
> = keyof ArgsByKey extends never
  ? never
  : SomeKnownKey<ArgsByKey> & { readonly [K in keyof ArgsByKey]?: Transitions<N, Ctx, B & ArgsByKey[K]> };

export type ReceivedEvents<Rs extends Events> = { readonly [K in keyof Rs]: { readonly payload: Payload<Rs[K]> } };

type RejectionBinding = { readonly kind: RejectionKind };

type Handled<N extends string, Ctx, A> =
  | readonly []
  | readonly [...Transitions<N, Ctx, A>, Transition<N, Ctx, A> & { readonly guard?: never }];

/**
 * The `onRejected` transitions, written exactly when an answer may be rejected: never for an external target that
 * declares `rejects: []`, always for another external target, and for a target of a spec service when its definition or
 * the sender's service allows a rejection (NonCanonical.missingOnRejected, NonCanonical.unreachableOnRejected; the type
 * cannot tell the sender's own service from another spec service, since a service has no type of its own). They are
 * empty, which ignores every rejection, or end with a transition without a guard, which takes every rejection that no
 * earlier guard takes (`{}` does nothing), so no rejection goes unhandled.
 */
type OnRejected<N extends string, Ctx, B, D> = D extends { readonly rejects: readonly [] }
  ? { readonly onRejected?: never }
  : D extends { readonly rejects: readonly RejectionKind[] }
    ? { readonly onRejected: Handled<N, Ctx, B & { readonly rejection: RejectionBinding }> }
    : { readonly onRejected?: Handled<N, Ctx, B & { readonly rejection: RejectionBinding }> };

/** The queries that a state calls; a state that does nothing on an answer writes `[]`. */
type StateCalls<N extends string, Ctx, B, Qs extends Queries> = SomeKnownKey<Qs> & {
  readonly [K in keyof Qs]?: {
    readonly onFulfilled: Transitions<N, Ctx, B & { readonly output: QueryOutput<Qs[K]> }>;
  } & OnRejected<N, Ctx, B, Qs[K]> &
    InputOf<Qs[K], B>;
};

/** The commands that a state sends; a state that does nothing on an answer writes `[]`. */
export type StateSends<N extends string, Ctx, B, Cs extends Commands> = SomeKnownKey<Cs> & {
  readonly [K in keyof Cs]?: {
    readonly onAccepted: Transitions<N, Ctx, B & AcceptedOutput<Cs[K]>>;
  } & OnRejected<N, Ctx, B, Cs[K]> &
    InputOf<Cs[K], B & CreateKey>;
};

interface NodeBase<N extends string, Ctx, B, Ons> {
  /** The transitions per received event, and in screens also per control name. */
  readonly on?: Ons;
  /**
   * The deadlines by name. An empty `after` is NonCanonical.emptyAfter and not a type error, as an empty `guard` is.
   */
  readonly after?: { readonly [deadline: string]: Deadline<N, Ctx, B> };
  readonly always?: Transitions<N, Ctx, B>;
  readonly entry?: { readonly assign: Assign<Ctx, B> };
  readonly exit?: { readonly assign: Assign<Ctx, B> };
}

interface ParentNode<N extends string, Ctx, B> {
  readonly onDone?: Transitions<N, Ctx, B>;
}

interface MapNode<B, Key> {
  /**
   * A function that returns the rows of the map state's key fields; each key appears once, and their order does not
   * matter.
   */
  readonly items: (args: B) => readonly Key[];
}

type MachineRequest<N extends string, Ctx, B, Qs extends Queries, Cs extends Commands> = {
  readonly calls?: StateCalls<N, Ctx, B, Qs>;
  readonly sends?: StateSends<N, Ctx, B, Cs>;
};

export type StateBehavior<Kd, N extends string, Ctx, B, Ons, Rq, Key = never> = Kd extends "final"
  ? Pick<NodeBase<N, Ctx, B, never>, "entry">
  : NodeBase<N, Ctx, B, Ons> &
      Rq &
      (Kd extends "parent" ? ParentNode<N, Ctx, B> : { readonly onDone?: never }) &
      (Kd extends "map" ? MapNode<B, Key> : { readonly items?: never });

type OuterArguments<Ctx extends DefaultedShape, Es extends Entities> = BaseArgs<Row<Ctx>, never, Records<Es>>;
type Ons<Ctx, N extends string, Rs extends Events, B> = KeyedTransitions<N, Ctx, B, ReceivedEvents<Rs>>;
/** The names, context, and arguments in scope of the state `K`. `KindArgs` are the arguments that only a screen has. */
export type Scope<F, K extends keyof F, Ctx extends Shape, D, KindArgs> = [MapOf<F, K>] extends [never]
  ? {
      readonly names: OuterNames<F>;
      readonly context: Row<Ctx>;
      readonly args: BaseArgs<Row<Ctx>, OutsideRegionOrMap<F, K, OuterNames<F>>, D> & KindArgs;
    }
  : CopyScope<F, K, MapOf<F, K>, FieldsOf<Ctx> & FieldsOf<CopyContext<F, MapOf<F, K>>>, D, KindArgs>;
/**
 * The row of a shape; for a shape without fields, an object without fields rather than Zod's `Record<string, never>`.
 */
type FieldsOf<S extends Shape> = [keyof S] extends [never] ? Record<never, never> : Row<S>;
type CopyScope<F, K extends keyof F, M, Ctx, D, KindArgs> = {
  readonly names: CopyNames<F, M>;
  readonly context: Ctx;
  readonly args: BaseArgs<Ctx, OutsideRegionOrMap<F, K, OuterNames<F> | CopyNames<F, M>>, D> &
    KindArgs & { readonly key: CopyKey<F, M> };
};
type MachineScope<F, K extends keyof F, Ctx extends DefaultedShape, Es extends Entities> = Scope<
  F,
  K,
  Ctx,
  Records<Es>,
  unknown
>;
type ScopeArgs<F, Ctx extends DefaultedShape, Es extends Entities> = {
  readonly [K in keyof F]: MachineScope<F, K, Ctx, Es>["args"];
};
type MachineBehaviors<
  F,
  Ctx extends DefaultedShape,
  Rs extends Events,
  Qs extends Queries,
  Cs extends Commands,
  Es extends Entities,
> = {
  readonly [K in keyof F]: MachineBehavior<
    F,
    K,
    MachineScope<F, K, Ctx, Es>,
    Rs,
    Qs,
    Cs,
    HeldArgs<MachineScope<F, K, Ctx, Es>["args"], F, K>
  >;
};
type MachineBehavior<
  F,
  K extends keyof F,
  S extends { readonly names: string; readonly context: unknown },
  Rs extends Events,
  Qs extends Queries,
  Cs extends Commands,
  B,
> = StateBehavior<
  KindOf<F, K>,
  S["names"],
  S["context"],
  B,
  Ons<S["context"], S["names"], Rs, B>,
  MachineRequest<S["names"], S["context"], B, Qs, Cs>,
  CopyKey<F, K>
>;
export type HeldArgs<B, F, K extends keyof F> = B & { readonly held: HeldIn<F, K> };

interface MachineSetup<
  Ctx extends DefaultedShape,
  Rs extends Events,
  Qs extends Queries,
  Cs extends Commands,
  Es extends Entities,
  F,
> {
  chart<const K extends TableKeys<F> = never>(
    definition: {
      /** The transitions that apply in every state. */
      on?: Ons<Row<Ctx>, OuterNames<F>, Rs, OuterArguments<Ctx, Es>>;
      states?: Table<F, K, ScopeArgs<F, Ctx, Es>, MachineBehaviors<F, Ctx, Rs, Qs, Cs, Es>> & SomeKey<K>;
    } & NoInfer<RowsWritten<F, K>>,
  ): Machine;
}

export type MachineDefiner<Es extends Entities> = <
  // St is not const: a const St keeps a nested initial as a literal, and its check against the children becomes never.
  St extends Tree,
  const Ctx extends DefaultedShape = Record<never, never>,
  const Rs extends Events = Record<never, never>,
  const Qs extends Queries = Record<never, never>,
  const Cs extends Commands = Record<never, never>,
  const Iv extends string = never,
>(
  setup: {
    description: string;
    context?: Ctx & SomeKey<keyof Ctx>;
    receives?: Rs & SomeKey<keyof Rs>;
    /** The queries of other services (Illegal.ownQuery). */
    queries?: Qs & SomeKey<keyof Qs>;
    commands?: Cs & SomeKey<keyof Cs>;
    initial: NoInfer<keyof St & string>;
    states: St & CheckTree<NoInfer<St>>;
    /**
     * The conditions on the context and on the states outside the copies of map states (Fault.failedChartInvariant).
     */
    invariants?: Named<Iv, { context: Row<Ctx>; active: { readonly [S in OuterNames<Flat<St>>]: boolean } }>;
  } & TreeErrors<St> &
    ErrorIf<"duplicateContextFields", SharedContextFields<Flat<St>, Ctx>>,
) => MachineSetup<Ctx, Rs, Qs, Cs, Es, Flat<St>>;

export function machineDefiner(owner: ServiceDefinition): MachineDefiner<Entities> {
  return (setup) => ({
    chart: (definition) => ({
      kind: "machine",
      service: owner,
      description: setup.description,
      context: setup.context ?? {},
      receives: setup.receives ?? {},
      queries: setup.queries ?? {},
      commands: setup.commands ?? {},
      initial: setup.initial,
      ...assemble(setup.states, definition.states ?? {}),
      on: (definition.on ?? {}) as unknown as Readonly<Record<string, readonly TransitionSpec[]>>,
      invariants: (setup.invariants ?? {}) as Conditions<unknown>,
    }),
  });
}
