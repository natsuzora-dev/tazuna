import type { z } from "zod";
import type { Bag, Made } from "../data/bag.ts";
import type { Shape } from "../data/values.ts";
import type { Named } from "./conditions.ts";
import {
  type AnyOffer,
  type AnyScreen,
  type Control,
  type Events,
  type InputOf,
  type NoneOffer,
  none,
  type QueryOutput,
  type Screen,
  type ServiceDefinition,
} from "./definition.ts";
import type { Entities, Immutable, MadeRow, Records, Row } from "./entity.ts";
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
  type ErrorIf,
  type Flat,
  type MapOf,
  type OuterNames,
  type RowsWritten,
  type SharedContextFields,
  type Table,
  type TableKeys,
  type TargetsOf,
  type Tree,
  type TreeErrors,
  type UnheldTop,
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

/** A control written with a payload has it, so that a `domain()` can name a payload field's schema. */
type ScreenControls<Ps extends Payloads> = {
  readonly [K in keyof Ps]: Ps[K] extends Shape
    ? Control<Ps[K]> & { readonly payload: Ps[K] }
    : Control<PayloadOf<Ps[K]>>;
};
type OperatedControls<Ps extends Payloads> = { readonly [K in keyof Ps]: { readonly payload: Row<PayloadOf<Ps[K]>> } };

/**
 * The queries that a state shows. A rejection other than unavailable is a fault of the screen (`Fault.rejectedShows`).
 */
type Shows<B, Qs extends Queries> = { readonly [K in keyof Qs]?: InputOf<Qs[K], B> };

type StateOpens<Targets, Ctx, B, Ss extends Screens> = {
  readonly [K in keyof Ss]?: {
    /** Whether the child opens as with HTML `showModal()` (true) or as with HTML `show()` (false). */
    readonly modal: boolean;
    readonly onDone: Transitions<Targets, Ctx, B & { readonly output: ScreenOutput<Ss[K]> }>;
  } & InputOf<Ss[K], B>;
};

type ScreenEntry<Targets, Ctx, B, Cs extends Commands, Ss extends Screens> = {
  readonly sends?: StateSends<Targets, Ctx, B, Cs>;
  readonly opens?: StateOpens<Targets, Ctx, B, Ss>;
};

type ScreenRequest<Targets, Ctx, B, Sh extends Queries, Cs extends Commands, Ss extends Screens> = {
  readonly shows?: Shows<B, Sh>;
} & ScreenEntry<Targets, Ctx, B, Cs, Ss>;
type CopyRequest<Targets, Ctx, B, Cs extends Commands> = Pick<ScreenEntry<Targets, Ctx, B, Cs, never>, "sends"> & {
  readonly shows?: never;
  readonly opens?: never;
};

type Ons<Targets, Ctx, B, Ps extends Payloads, Rs extends Events> = KeyedTransitions<
  Targets,
  Ctx,
  B,
  OperatedControls<Ps> & ReceivedEvents<Rs>
>;

type ScreenResolve<O extends Shape, A> = keyof O extends never
  ? { resolve?: never }
  : { resolve: (args: A) => MadeRow<O> };

type RequiredKeys<S extends Shape> = { [K in keyof S]: S[K] extends z.ZodDefault<z.ZodType> ? never : K }[keyof S];
type InitialContext<S extends Shape> = { readonly [K in RequiredKeys<S>]: Made<Immutable<z.output<S[K]>>> } & {
  readonly [K in Exclude<keyof S, RequiredKeys<S>>]?: Made<Immutable<z.output<S[K]>>>;
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
  S extends { readonly targets: unknown; readonly context: unknown },
  B,
> = StateBehavior<
  F,
  K,
  S["targets"],
  S["context"],
  B,
  Ons<S["targets"], S["context"], B, Ps, Rs>,
  ([MapOf<F, K>] extends [never]
    ? ScreenRequest<S["targets"], S["context"], B, Sh, Cs, Ss>
    : CopyRequest<S["targets"], S["context"], B, Cs>) &
    StateOffers<Ps, B>
>;
/**
 * The payloads that the user can choose for a control: `any` offers every payload that matches the schema, `none`
 * offers nothing, and a function returns the payloads that it offers at that point (`NonCanonical.constantOffer`).
 */
type Offer<P, A> = ((args: A) => Bag<MadeRow<PayloadOf<P>>> | readonly MadeRow<PayloadOf<P>>[]) | AnyOffer | NoneOffer;

/** The offers of a state, which override the offers of its ancestors and of the chart for the controls they name. */
type StateOffers<Ps extends Payloads, A> = {
  readonly offers?: [keyof Ps] extends [never] ? never : { readonly [K in keyof Ps]?: Offer<Ps[K], A> };
};

/** The chart's own offers, which name every control, so that no control is offered without a written entry. */
type ChartOffers<Ps extends Payloads, A> = [keyof Ps] extends [never]
  ? { readonly offers?: never }
  : { readonly offers: { readonly [K in keyof Ps]: Offer<Ps[K], A> } };

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
    definition: ChartOffers<Ps, OuterArguments<I, Ctx, Sh, Es>> &
      InitialContextSetup<I, Ctx, R> &
      ScreenResolve<O, OuterArguments<I, Ctx, Sh, Es>> & {
        /** The transitions that apply in every state. */
        on?: NoInfer<Ons<TargetsOf<F, OuterNames<F>>, Row<Ctx>, OuterArguments<I, Ctx, Sh, Es>, Ps, Rs>>;
        states?: Table<F, K, ScreenBehaviors<F, I, Ctx, Rs, Sh, Cs, Ss, Es, Ps>>;
      } & NoInfer<RowsWritten<F, K>>,
  ): Screen<I, O, ScreenControls<Ps>>;
}

export type ScreenDefiner<Es extends Entities> = <
  // St is const so that a nested initial stays a literal, which names the child that the initial edge fills.
  const St extends Tree,
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
     * `ensures` (`Illegal.missingParent`).
     */
    input?: I;
    output?: O;
    /** A field without a default starts from `initialContext`. */
    context?: Ctx;
    receives?: Rs;
    queries?: Sh;
    commands?: Cs;
    screens?: Ss;
    controls?: {
      readonly [K in keyof Ps]: { readonly label: string; readonly payload?: Ps[K] & Shape };
    } & { readonly [K in keyof NoInfer<Rs>]?: never };
    initial: NoInfer<UnheldTop<St>>;
    states: St & CheckTree<NoInfer<St>>;
    requires?: Named<Rq, { input: Row<I> }>;
    ensures?: Named<En, { input: Row<I>; output: Row<O> }>;
    /**
     * The conditions on the context and on the states outside the copies of map states (`Fault.failedChartInvariant`).
     */
    invariants?: Named<Iv, { context: Row<Ctx>; active: { readonly [S in OuterNames<Flat<St>>]: boolean } }>;
  } & TreeErrors<St> &
    ErrorIf<"duplicateContextFields", SharedContextFields<Flat<St>, Ctx>>,
) => ScreenSetup<I, O, Ctx, Rs, Sh, Cs, Ss, Es, Ps, Flat<St>>;

/** `offers` with `none` written as the function that lists no payload, which is what it offers. */
const listed = (offers: object) =>
  Object.fromEntries(Object.entries(offers).map(([control, o]) => [control, o === none ? () => [] : o]));

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
        ...assemble(
          setup.states,
          Object.fromEntries(
            Object.entries((definition.states ?? {}) as Readonly<Record<string, { readonly offers?: object }>>).map(
              ([name, row]) => [name, row.offers === undefined ? row : { ...row, offers: listed(row.offers) }],
            ),
          ),
        ),
        ...(definition.offers === undefined ? {} : { offers: listed(definition.offers) }),
        on: definition.on ?? {},
        invariants: setup.invariants ?? {},
        requires: setup.requires ?? {},
        ensures: setup.ensures ?? {},
        ...(definition.resolve === undefined ? {} : { resolve: definition.resolve }),
      }) as never,
  });
}
