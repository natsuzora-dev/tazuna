import type { Bag, Made } from "../data/bag.ts";
import type { RejectionKind } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import type { Conditions, Named } from "./conditions.ts";
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
  type InitialEdge,
  type InitialHeldIn,
  type KindOf,
  type MapOf,
  type OuterNames,
  type OutsideRegionOrMap,
  type RowsWritten,
  type SharedContextFields,
  type Table,
  type TableKeys,
  type TargetsOf,
  type Tree,
  type TreeErrors,
  type UnheldTop,
  type With,
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

type Assign<Ctx, A> = { readonly [K in keyof Ctx]?: (args: A & CreateKey) => Made<Ctx[K]> };

/**
 * `with` when the target `H` has parameters, written exactly then: the edge that enters a state fills its parameters,
 * which stay fixed until it exits.
 */
type WithFor<H, A> = [keyof H] extends [never] ? { readonly with?: never } : { readonly with: With<H, A> };

/** The target `S` of a transition, which fills the parameters `H` of `S` when it enters `S`. */
type Target<S, H, A> = {
  readonly target: S;
  /**
   * Whether the transition exits and re-enters its source state. Written exactly when `target` is the state that writes
   * the transition or a descendant of that state (`NonCanonical.missingReenter`, `NonCanonical.reenterOnRoot`,
   * `NonCanonical.reenterOutsideSource`).
   */
  readonly reenter?: boolean;
} & WithFor<H, A>;

/**
 * The parameters `H` of the state that writes a transition, as its own target. Only `reenter: true` exits and enters
 * it again, so only then does `with` fill `H`; otherwise the state keeps them.
 */
interface Own<H> {
  readonly own: H;
}

/**
 * The target `S` of a transition written in `S` itself, with its parameters `H`: `with` comes exactly with
 * `reenter: true`.
 */
type OwnTarget<S, H, A> = [keyof H] extends [never]
  ? Target<S, H, A>
  :
      | (Target<S, H, A> & { readonly reenter: true })
      | { readonly target: S; readonly reenter?: false; readonly with?: never };

/** `Targets` for a transition written in state `K`, which marks `K`'s parameters as its own (`Own`). */
type TargetsFrom<Targets, K> = { readonly [S in keyof Targets]: S extends K ? Own<Targets[S]> : Targets[S] };

/**
 * A transition. `Targets` maps each state that it may target to the parameters of that state (`TargetsOf`), or the
 * state that writes it to its own (`TargetsFrom`).
 */
type Transition<Targets, Ctx, A> = {
  /**
   * The conditions of the transition. When a guard checks the same condition as a `requires` of a command that the
   * state sends: for another service's records, read that service's query answer (`shown` or a `calls` answer). For the
   * own service's records, call the `condition` that the `requires` calls. For values that only the sender holds
   * (`context`, `payload`), write the same expression in the guard.
   */
  readonly guard?: Conditions<A>;
  readonly assign?: Assign<Ctx, A>;
} & (
  | {
      [S in keyof Targets & string]: Targets[S] extends Own<infer H> ? OwnTarget<S, H, A> : Target<S, Targets[S], A>;
    }[keyof Targets & string]
  | { readonly target?: never; readonly reenter?: never; readonly with?: never }
);
export type Transitions<Targets, Ctx, A> = readonly Transition<Targets, Ctx, A>[];
type NoAt = { readonly at?: never };
type NoDelay = { readonly delay?: never };
/**
 * A deadline, its time fixed when the state is entered: `now` plus `delay` milliseconds, or the instant that `at`
 * computes. `at` does not read `now`, because a fixed length from now is a `delay`. To move a deadline, enter its state again (`reenter: true`).
 */
type Deadline<Targets, Ctx, A> = {
  readonly onFired: Transitions<Targets, Ctx, A>;
} & (({ readonly delay: number } & NoAt) | ({ readonly at: (args: Omit<A, "now">) => number } & NoDelay));
export type Queries = Readonly<Record<string, AnyQuery>>;
export type Commands = Readonly<Record<string, AnyCommand>>;

export type KeyedTransitions<
  Targets,
  Ctx,
  B,
  ArgsByKey extends Readonly<Record<string, object>>,
> = keyof ArgsByKey extends never
  ? never
  : { readonly [K in keyof ArgsByKey]?: Transitions<Targets, Ctx, B & ArgsByKey[K]> };

export type ReceivedEvents<Rs extends Events> = { readonly [K in keyof Rs]: { readonly payload: Payload<Rs[K]> } };

type RejectionBinding = { readonly kind: RejectionKind };

type Handled<Targets, Ctx, A> =
  | readonly []
  | readonly [...Transitions<Targets, Ctx, A>, Transition<Targets, Ctx, A> & { readonly guard?: never }];

/**
 * The `onRejected` transitions, written exactly when an answer may be rejected (`NonCanonical.missingOnRejected`,
 * `NonCanonical.unreachableOnRejected`). They are empty, which ignores every rejection, or end with a transition without
 * a guard, which takes every rejection that no earlier guard takes (`{}` does nothing), so no rejection goes unhandled.
 */
type OnRejected<Targets, Ctx, B> = {
  readonly onRejected?: Handled<Targets, Ctx, B & { readonly rejection: RejectionBinding }>;
};

/** The queries that a state calls. A state that does nothing on an answer writes `[]`. */
type StateCalls<Targets, Ctx, B, Qs extends Queries> = {
  readonly [K in keyof Qs]?: {
    readonly onFulfilled: Transitions<Targets, Ctx, B & { readonly output: QueryOutput<Qs[K]> }>;
  } & OnRejected<Targets, Ctx, B> &
    InputOf<Qs[K], B>;
};

/** The commands that a state sends. A state that does nothing on an answer writes `[]`. */
export type StateSends<Targets, Ctx, B, Cs extends Commands> = {
  readonly [K in keyof Cs]?: {
    readonly onAccepted: Transitions<Targets, Ctx, B & AcceptedOutput<Cs[K]>>;
  } & OnRejected<Targets, Ctx, B> &
    InputOf<Cs[K], B & CreateKey>;
};

interface NodeBase<Targets, Ctx, B, Ons> {
  /** The transitions per received event, and in screens also per control name. */
  readonly on?: Ons;
  /** The deadlines by name. */
  readonly after?: { readonly [deadline: string]: Deadline<Targets, Ctx, B> };
  readonly always?: Transitions<Targets, Ctx, B>;
  readonly entry?: { readonly assign: Assign<Ctx, B> };
  readonly exit?: { readonly assign: Assign<Ctx, B> };
}

interface ParentNode<Targets, Ctx, B> {
  readonly onDone?: Transitions<Targets, Ctx, B>;
}

interface MapNode<B, Key> {
  /**
   * A function that returns the rows of the map state's key fields. Each key appears once, and their order does not
   * matter.
   */
  readonly items: (args: B) => Bag<Key> | readonly Key[];
}

type MachineRequest<Targets, Ctx, B, Qs extends Queries, Cs extends Commands> = {
  readonly calls?: StateCalls<Targets, Ctx, B, Qs>;
  readonly sends?: StateSends<Targets, Ctx, B, Cs>;
};

/**
 * The behavior of the state `K` of the flat tree `F`. The initial edge of a parent fills the parameters of its initial
 * child; a map state's initial edge starts each copy, so its `with` reads the copy's `key`.
 */
export type StateBehavior<F, K extends keyof F, Targets, Ctx, B, Ons, Rq> =
  KindOf<F, K> extends "final"
    ? Pick<NodeBase<Targets, Ctx, B, never>, "entry">
    : NodeBase<Targets, Ctx, B, Ons> &
        Rq &
        (KindOf<F, K> extends "parent" ? ParentNode<Targets, Ctx, B> : { readonly onDone?: never }) &
        (KindOf<F, K> extends "map" ? MapNode<B, CopyKey<F, K>> : { readonly items?: never }) &
        InitialEdge<InitialHeldIn<F, K>, KindOf<F, K> extends "map" ? B & { readonly key: CopyKey<F, K> } : B>;

type OuterArguments<Ctx extends DefaultedShape, Es extends Entities> = BaseArgs<Row<Ctx>, never, Records<Es>>;
type Ons<Ctx, Targets, Rs extends Events, B> = KeyedTransitions<Targets, Ctx, B, ReceivedEvents<Rs>>;
/** The targets, context, and arguments in scope of the state `K`. `KindArgs` are the arguments that only a screen has. */
export type Scope<F, K extends keyof F, Ctx extends Shape, D, KindArgs> = [MapOf<F, K>] extends [never]
  ? {
      readonly targets: TargetsFrom<TargetsOf<F, OuterNames<F>>, K>;
      readonly context: Row<Ctx>;
      readonly args: BaseArgs<Row<Ctx>, OutsideRegionOrMap<F, K, OuterNames<F>>, D> & KindArgs;
    }
  : CopyScope<F, K, MapOf<F, K>, FieldsOf<Ctx> & FieldsOf<CopyContext<F, MapOf<F, K>>>, D, KindArgs>;
/**
 * The row of a shape. For a shape without fields, an object without fields rather than Zod's `Record<string, never>`.
 */
type FieldsOf<S extends Shape> = [keyof S] extends [never] ? Record<never, never> : Row<S>;
type CopyScope<F, K extends keyof F, M, Ctx, D, KindArgs> = {
  readonly targets: TargetsFrom<TargetsOf<F, CopyNames<F, M>>, K>;
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
  S extends { readonly targets: unknown; readonly context: unknown },
  Rs extends Events,
  Qs extends Queries,
  Cs extends Commands,
  B,
> = StateBehavior<
  F,
  K,
  S["targets"],
  S["context"],
  B,
  Ons<S["context"], S["targets"], Rs, B>,
  MachineRequest<S["targets"], S["context"], B, Qs, Cs>
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
      on?: Ons<Row<Ctx>, TargetsOf<F, OuterNames<F>>, Rs, OuterArguments<Ctx, Es>>;
      states?: Table<F, K, MachineBehaviors<F, Ctx, Rs, Qs, Cs, Es>>;
    } & NoInfer<RowsWritten<F, K>>,
  ): Machine;
}

export type MachineDefiner<Es extends Entities> = <
  // St is const so that a nested initial stays a literal, which names the child that the initial edge fills.
  const St extends Tree,
  const Ctx extends DefaultedShape = Record<never, never>,
  const Rs extends Events = Record<never, never>,
  const Qs extends Queries = Record<never, never>,
  const Cs extends Commands = Record<never, never>,
  const Iv extends string = never,
>(
  setup: {
    description: string;
    context?: Ctx;
    receives?: Rs;
    /** The queries of other services (`Illegal.ownQuery`). */
    queries?: Qs;
    commands?: Cs;
    initial: NoInfer<UnheldTop<St>>;
    states: St & CheckTree<NoInfer<St>>;
    /**
     * The conditions on the context and on the states outside the copies of map states (`Fault.failedChartInvariant`).
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
