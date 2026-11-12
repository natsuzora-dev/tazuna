import type { z } from "zod";
import type { Shape } from "../data/values.ts";
import type { Named, SomeKey } from "./conditions.ts";
import type { AnyScreen, Control, Events, InputOf, QueryOutput, Screen, ServiceDefinition } from "./definition.ts";
import type { Entities, Immutable, Records, Row } from "./entity.ts";
import type {
  BaseArgs,
  Commands,
  HeldArgs,
  KeyedTransitions,
  Queries,
  ReceivedEvents,
  Scope,
  StateBehavior,
  StateSends,
  Transitions,
} from "./machine.ts";
import {
  assemble,
  type CheckTree,
  type CopyKey,
  type ErrorIf,
  type Flat,
  type KindOf,
  type MapOf,
  type OuterNames,
  type RowsWritten,
  type SharedContextFields,
  type SomeKnownKey,
  type Table,
  type TableKeys,
  type Tree,
  type TreeErrors,
} from "./tree.ts";

type Screens = Readonly<Record<string, AnyScreen>>;

type Shown<Sh extends Queries> = { readonly [K in keyof Sh]: QueryOutput<Sh[K]> | null };
type Payloads = Readonly<Record<string, unknown>>;
type PayloadOf<P> = P extends Shape ? P : Record<never, never>;

type ScreenFields<I extends Shape, Sh extends Queries> = {
  readonly input: Row<I>;
  /** The output of the latest fulfilled answer to each query that the screen shows. */
  readonly shown: Shown<Sh>;
};

type ScreenOutput<S> = S extends Screen<Shape, infer O> ? Row<O> : never;

type ScreenControls<Ps extends Payloads> = { readonly [K in keyof Ps]: Control<PayloadOf<Ps[K]>> };
type OperatedControls<Ps extends Payloads> = { readonly [K in keyof Ps]: { readonly payload: Row<PayloadOf<Ps[K]>> } };

/**
 * The queries that a state shows. A rejection other than unavailable is a fault of the screen (Fault.rejectedShows).
 */
type Shows<B, Qs extends Queries> = SomeKnownKey<Qs> & { readonly [K in keyof Qs]?: InputOf<Qs[K], B> };

type StateOpens<N extends string, Ctx, B, Ss extends Screens> = SomeKnownKey<Ss> & {
  readonly [K in keyof Ss]?: {
    /** Whether the child opens as with HTML `showModal()` (true) or as with HTML `show()` (false). */
    readonly modal: boolean;
    readonly onDone: Transitions<N, Ctx, B & { readonly output: ScreenOutput<Ss[K]> }>;
  } & InputOf<Ss[K], B>;
};

type ScreenEntry<N extends string, Ctx, B, Cs extends Commands, Ss extends Screens> = {
  readonly sends?: StateSends<N, Ctx, B, Cs>;
  readonly opens?: StateOpens<N, Ctx, B, Ss>;
};

type ScreenRequest<N extends string, Ctx, B, Sh extends Queries, Cs extends Commands, Ss extends Screens> = {
  readonly shows?: Shows<B, Sh>;
} & ScreenEntry<N, Ctx, B, Cs, Ss>;
type CopyRequest<N extends string, Ctx, B, Cs extends Commands> = Pick<ScreenEntry<N, Ctx, B, Cs, never>, "sends"> & {
  readonly shows?: never;
  readonly opens?: never;
};

type Ons<N extends string, Ctx, B, Ps extends Payloads, Rs extends Events> = KeyedTransitions<
  N,
  Ctx,
  B,
  OperatedControls<Ps> & ReceivedEvents<Rs>
>;

type ScreenResolve<O extends Shape, A> = keyof O extends never ? { resolve?: never } : { resolve: (args: A) => Row<O> };

type RequiredKeys<S extends Shape> = { [K in keyof S]: S[K] extends z.ZodDefault<z.ZodType> ? never : K }[keyof S];
type InitialContext<S extends Shape> = { readonly [K in RequiredKeys<S>]: Immutable<z.output<S[K]>> } & {
  readonly [K in Exclude<keyof S, RequiredKeys<S>>]?: Immutable<z.output<S[K]>>;
};
type NoExtra<R, S extends Shape> = { readonly [K in Exclude<keyof R, keyof S>]: never };
type InitialContextOf<I extends Shape, Ctx extends Shape, R> = (args: {
  readonly input: Row<I>;
}) => R & NoExtra<R, Ctx>;
type InitialContextSetup<I extends Shape, Ctx extends Shape, R> = [RequiredKeys<Ctx>] extends [never]
  ? { initialContext?: InitialContextOf<I, Ctx, R> }
  : { initialContext: InitialContextOf<I, Ctx, R> };

type OuterArguments<I extends Shape, Ctx extends Shape, Sh extends Queries, Es extends Entities> = BaseArgs<
  Row<Ctx>,
  never,
  Records<Es>
> &
  ScreenFields<I, Sh>;
type ScreenScope<
  F,
  K extends keyof F,
  I extends Shape,
  Ctx extends Shape,
  Sh extends Queries,
  Es extends Entities,
> = Scope<F, K, Ctx, Records<Es>, ScreenFields<I, Sh>>;
type ScreenBehaviors<
  F,
  I extends Shape,
  Ctx extends Shape,
  Rs extends Events,
  Sh extends Queries,
  Cs extends Commands,
  Ss extends Screens,
  Es extends Entities,
  Ps extends Payloads,
> = {
  readonly [K in keyof F]: ScreenBehavior<
    F,
    K,
    Rs,
    Sh,
    Cs,
    Ss,
    Ps,
    ScreenScope<F, K, I, Ctx, Sh, Es>,
    HeldArgs<ScreenScope<F, K, I, Ctx, Sh, Es>["args"], F, K>
  >;
};
type ScreenBehavior<
  F,
  K extends keyof F,
  Rs extends Events,
  Sh extends Queries,
  Cs extends Commands,
  Ss extends Screens,
  Ps extends Payloads,
  S extends { readonly names: string; readonly context: unknown },
  B,
> = StateBehavior<
  KindOf<F, K>,
  S["names"],
  S["context"],
  B,
  Ons<S["names"], S["context"], B, Ps, Rs>,
  ([MapOf<F, K>] extends [never]
    ? ScreenRequest<S["names"], S["context"], B, Sh, Cs, Ss>
    : CopyRequest<S["names"], S["context"], B, Cs>) &
    StateOffers<Ps, B>,
  CopyKey<F, K>
>;
/** The payloads that a state offers; the chart's own offers are the root's. */
type StateOffers<Ps extends Payloads, A> = {
  /** The payloads that the user can choose: `[{}]` offers a control without payload fields; `[]` offers nothing. */
  readonly offers?: [keyof Ps] extends [never]
    ? never
    : SomeKnownKey<{ readonly [K in keyof Ps]: unknown }> & {
        readonly [K in keyof Ps]?: (args: A) => readonly Row<PayloadOf<Ps[K]>>[];
      };
};

interface ScreenSetup<
  I extends Shape,
  O extends Shape,
  Ctx extends Shape,
  Rs extends Events,
  Sh extends Queries,
  Cs extends Commands,
  Ss extends Screens,
  Es extends Entities,
  Ps extends Payloads,
  F,
> {
  chart<const K extends TableKeys<F> = never, const R extends InitialContext<Ctx> = InitialContext<Ctx>>(
    definition: StateOffers<Ps, OuterArguments<I, Ctx, Sh, Es>> &
      InitialContextSetup<I, Ctx, R> &
      ScreenResolve<O, OuterArguments<I, Ctx, Sh, Es>> & {
        /** The transitions that apply in every state. */
        on?: NoInfer<Ons<OuterNames<F>, Row<Ctx>, OuterArguments<I, Ctx, Sh, Es>, Ps, Rs>>;
        states?: Table<
          F,
          K,
          { readonly [P in keyof F]: ScreenScope<F, P, I, Ctx, Sh, Es>["args"] },
          ScreenBehaviors<F, I, Ctx, Rs, Sh, Cs, Ss, Es, Ps>
        > &
          SomeKey<K>;
      } & NoInfer<RowsWritten<F, K>>,
  ): Screen<I, O, ScreenControls<Ps>>;
}

export type ScreenDefiner<Es extends Entities> = <
  // St is not const: a const St keeps a nested initial as a literal, and its check against the children becomes never.
  St extends Tree,
  const I extends Shape = Record<never, never>,
  const O extends Shape = Record<never, never>,
  const Ctx extends Shape = Record<never, never>,
  const Rs extends Events = Record<never, never>,
  const Sh extends Queries = Record<never, never>,
  const Cs extends Commands = Record<never, never>,
  const Ss extends Screens = Record<never, never>,
  const Ps extends Payloads = Record<never, never>,
  const Rq extends string = never,
  const En extends string = never,
  const Iv extends string = never,
>(
  setup: {
    description: string;
    /**
     * The input of a screen that another screen opens. Only such a screen has `input`, `output`, `requires`, and
     * `ensures` (Illegal.keysWithoutParent).
     */
    input?: I & SomeKey<keyof I>;
    output?: O & SomeKey<keyof O>;
    /** A field without a default starts from `initialContext`. */
    context?: Ctx & SomeKey<keyof Ctx>;
    receives?: Rs & SomeKey<keyof Rs>;
    queries?: Sh & SomeKey<keyof Sh>;
    commands?: Cs & SomeKey<keyof Cs>;
    screens?: Ss & SomeKey<keyof Ss>;
    controls?: {
      readonly [K in keyof Ps]: { readonly label: string; readonly payload?: Ps[K] & Shape & SomeKey<keyof Ps[K]> };
    } & { readonly [K in keyof NoInfer<Rs>]?: never } & SomeKey<keyof Ps>;
    initial: NoInfer<keyof St & string>;
    states: St & CheckTree<NoInfer<St>>;
    requires?: Named<Rq, { input: Row<I> }>;
    ensures?: Named<En, { input: Row<I>; output: Row<O> }>;
    /**
     * The conditions on the context and on the states outside the copies of map states (Fault.failedChartInvariant).
     */
    invariants?: Named<Iv, { context: Row<Ctx>; active: { readonly [S in OuterNames<Flat<St>>]: boolean } }>;
  } & TreeErrors<St> &
    ErrorIf<"duplicateContextFields", SharedContextFields<Flat<St>, Ctx>>,
) => ScreenSetup<I, O, Ctx, Rs, Sh, Cs, Ss, Es, Ps, Flat<St>>;

export function screenDefiner(owner: ServiceDefinition): ScreenDefiner<Entities> {
  return (setup) => ({
    chart: (definition) =>
      ({
        kind: "screen",
        service: owner,
        description: setup.description,
        input: setup.input ?? {},
        output: setup.output ?? {},
        context: setup.context ?? {},
        ...(definition.initialContext === undefined ? {} : { initialContext: definition.initialContext }),
        receives: setup.receives ?? {},
        queries: setup.queries ?? {},
        commands: setup.commands ?? {},
        screens: setup.screens ?? {},
        controls: setup.controls ?? {},
        initial: setup.initial,
        ...assemble(setup.states, definition.states ?? {}),
        ...(definition.offers === undefined ? {} : { offers: definition.offers }),
        on: definition.on ?? {},
        invariants: setup.invariants ?? {},
        requires: setup.requires ?? {},
        ensures: setup.ensures ?? {},
        ...(definition.resolve === undefined ? {} : { resolve: definition.resolve }),
      }) as never,
  });
}
