import type { Bag } from "../data/bag.ts";
import type { Delay } from "../data/datetime.ts";
import type { RejectionKind } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import { definitionKinds } from "../syntax/structure.ts";
import type { Conditions } from "./conditions.ts";
import type { AnyEntity, AnyKeyedEntity, Entities, KeyOf, KeyValue, MadeRow, Ref, Row, RowOf } from "./entity.ts";

export type Definition = AnyEntity | AnyEvent | AnyCommand | AnyQuery | Automation | Machine | AnyScreen;

const kinds = new Set<unknown>(definitionKinds);

export function isDefinition(value: unknown): value is Definition {
  return typeof value === "object" && value !== null && kinds.has((value as { readonly kind?: unknown }).kind);
}

export interface Place {
  /** The file, relative to the spec folder. */
  readonly file: string;
  readonly line: number;
  readonly column: number;
}

export interface Named<D> {
  readonly name: string;
  /** The service of the definer that made the definition, or the service listing the entity in `entities`. */
  readonly service: string;
  readonly place: Place;
  readonly definition: D;
}

type ByName<N extends string, F> = { readonly [K in N]: F };

export interface Command<
  I extends Shape = Shape,
  Ev extends AnyEvent = AnyEvent,
  Bn extends string = string,
  Rq extends string = string,
  O extends Shape | undefined = Shape | undefined,
  Rj extends readonly RejectionKind[] | undefined = readonly RejectionKind[] | undefined,
> {
  readonly kind: "command";
  readonly service: ServiceDefinition;
  readonly input: I;
  /** The output shape, or undefined for a command without output. */
  readonly output: O;
  readonly emits: readonly Ev[];
  readonly binds: ByName<Bn, (args: never) => unknown>;
  readonly requires: ByName<Rq, (args: never) => boolean>;
  readonly ensures: Conditions<never>;
  /** The decide function, or undefined for a command of an external service. */
  readonly decide: ((args: never) => Emits) | undefined;
  /** The declared rejection kinds, or undefined for a command of a spec service. */
  readonly rejects: Rj;
}

export interface Query<
  I extends Shape = Shape,
  O extends Shape = Shape,
  Rq extends string = string,
  Rj extends readonly RejectionKind[] | undefined = readonly RejectionKind[] | undefined,
> {
  readonly kind: "query";
  readonly service: ServiceDefinition;
  readonly input: I;
  readonly output: O;
  readonly requires: ByName<Rq, (args: never) => boolean>;
  readonly ensures: Conditions<never>;
  /** The resolve function, or undefined for a query of an external service. */
  readonly resolve: ((args: never) => unknown) | undefined;
  /** The declared rejection kinds, or undefined for a query of a spec service. */
  readonly rejects: Rj;
}

/** A command of any shape. */
// biome-ignore lint/suspicious/noExplicitAny: a command of any shape
export type AnyCommand = Command<any, any, any, any, any, any>;

/** A query of any shape. */
// biome-ignore lint/suspicious/noExplicitAny: a query of any shape
export type AnyQuery = Query<any, any, any, any>;

export type QueryOutput<Q extends AnyQuery> = Q extends Query<Shape, infer O> ? Row<O> : never;

export type AcceptedOutput<C extends AnyCommand> =
  C extends Command<Shape, AnyEvent, string, string, infer O>
    ? [O] extends [undefined]
      ? unknown
      : O extends Shape
        ? { readonly output: Row<O> }
        : never
    : never;

type InputShape<D> = D extends { readonly input: infer I extends Shape } ? I : never;

export type InputOf<D, Args> = keyof InputShape<D> extends never
  ? { input?: (args: Args) => MadeRow<InputShape<D>> }
  : { input: (args: Args) => MadeRow<InputShape<D>> };

/** Named expressions whose values later expressions read as `bound`. */
export type Binds<Args, B = Record<string, unknown>> = { readonly [K in keyof B]: (args: Args) => B[K] };

export interface Automation {
  readonly kind: "automation";
  readonly service: ServiceDefinition;
  /** The received event. `receives` and `commands` each hold one entry, as written. */
  readonly receives: Readonly<Record<string, AnyEvent>>;
  readonly commands: Readonly<Record<string, AnyCommand>>;
  readonly binds: Binds<never>;
  readonly guard: Conditions<never>;
  readonly input: ((args: never) => unknown) | undefined;
  readonly onRejected: readonly [] | undefined;
}

export interface ServiceDefinition {
  readonly kind: "service";
  readonly description: string;
  readonly entities: Entities;
  readonly invariants: Conditions<never>;
  readonly external: boolean;
}

export interface Now {
  /** The time of the message in progress. */
  readonly now: Temporal.Instant;
}

/** The function that creates a new key; the implementation decides the key's form. */
export type CreateKey = { readonly createKey: <E extends AnyKeyedEntity>(key: Ref<E>) => KeyValue<E> };

export interface CreateEvent<E extends AnyKeyedEntity = AnyKeyedEntity> {
  readonly kind: "event";
  readonly service: ServiceDefinition;
  readonly change: "create";
  readonly entity: E;
  readonly payload: Shape;
}

export interface UpdateEvent<E extends AnyEntity = AnyEntity, W extends string = string> {
  readonly kind: "event";
  readonly service: ServiceDefinition;
  readonly change: "update";
  readonly entity: E;
  readonly writes: readonly W[];
  readonly payload: Shape;
}

export interface DeleteEvent<E extends AnyKeyedEntity = AnyKeyedEntity> {
  readonly kind: "event";
  readonly service: ServiceDefinition;
  readonly change: "delete";
  readonly entity: E;
  readonly payload: Shape;
}

export interface FieldsEvent<S extends Shape = Shape> {
  readonly kind: "event";
  readonly change: "none";
  readonly service: ServiceDefinition;
  readonly payload: S;
}

// biome-ignore lint/suspicious/noExplicitAny: an event of any shape
export type AnyEvent = CreateEvent<any> | UpdateEvent<any, any> | DeleteEvent<any> | FieldsEvent<any>;

type KeyPayload<E extends AnyEntity> = E extends AnyKeyedEntity ? { [K in KeyOf<E>]: KeyValue<E> } : unknown;

export type Payload<Ev extends AnyEvent> =
  Ev extends CreateEvent<infer E>
    ? RowOf<E>
    : Ev extends UpdateEvent<infer E, infer W>
      ? KeyPayload<E> & Pick<RowOf<E>, W & keyof RowOf<E>>
      : Ev extends DeleteEvent<infer E>
        ? KeyPayload<E>
        : Ev extends FieldsEvent<infer S>
          ? Row<S>
          : never;

export interface Emit<Ev extends AnyEvent = AnyEvent> {
  readonly kind: "emit";
  readonly event: Ev;
  readonly payload: Payload<Ev>;
}

/**
 * The events of a command's `decide`, in order. A Bag of events has no order inside, and two of its events must not
 * write one record.
 */
export type Emits<Ev extends AnyEvent = AnyEvent> = readonly (Emit<Ev> | Bag<Emit<Ev>>)[];

export interface TransitionSpec {
  readonly target?: string;
  readonly guard?: Conditions<unknown>;
  readonly assign?: AssignSpec;
  readonly reenter?: boolean;
}

interface DeadlineSpec {
  readonly delay?: Delay;
  readonly at?: (args: unknown) => Temporal.Instant;
  readonly onFired: readonly TransitionSpec[];
}

type AssignSpec = Readonly<Record<string, (args: unknown) => unknown>>;

interface RequestSpec {
  readonly input?: (args: unknown) => unknown;
  readonly onRejected?: readonly TransitionSpec[];
}

type Keyed<T> = Readonly<Record<string, T>>;

type Offers = Keyed<(args: unknown) => readonly unknown[]>;

export interface StateSpec {
  readonly type?: "parallel" | "map" | "final" | "history";
  readonly key?: Shape;
  readonly context?: Shape;
  readonly items?: (args: unknown) => readonly unknown[];
  readonly initial?: string;
  readonly states?: Readonly<Record<string, StateSpec>>;
  readonly offers?: Offers;
  readonly on?: Readonly<Record<string, readonly TransitionSpec[]>>;
  readonly after?: Keyed<DeadlineSpec>;
  readonly always?: readonly TransitionSpec[];
  readonly entry?: { readonly assign: AssignSpec };
  readonly exit?: { readonly assign: AssignSpec };
  readonly onDone?: readonly TransitionSpec[];
  readonly calls?: Keyed<RequestSpec & { readonly onFulfilled: readonly TransitionSpec[] }>;
  readonly sends?: Keyed<RequestSpec & { readonly onAccepted: readonly TransitionSpec[] }>;
  readonly shows?: Keyed<{ readonly input?: (args: unknown) => unknown }>;
  readonly opens?: Keyed<{
    readonly modal: boolean;
    readonly input?: (args: unknown) => unknown;
    readonly onDone: readonly TransitionSpec[];
  }>;
}

export interface ChartSpec {
  readonly kind: "machine" | "screen";
  readonly context: Shape;
  /** A function that returns the context fields without a default. */
  readonly initialContext?: (args: { readonly input: Readonly<Record<string, unknown>> }) => unknown;
  readonly input?: Shape;
  readonly output?: Shape;
  readonly controls?: Readonly<Record<string, AnyControl>>;
  readonly receives: Events;
  readonly queries?: Readonly<Record<string, AnyQuery>>;
  readonly commands: Readonly<Record<string, AnyCommand>>;
  readonly screens?: Readonly<Record<string, AnyScreen>>;
  /** The shapes of the values that each state holds, per state name. */
  readonly held?: Readonly<Record<string, Shape>>;
  /** The expressions of the values that each state holds, per state name. */
  readonly holds?: Readonly<Record<string, Readonly<Record<string, (args: unknown) => unknown>>>>;
  readonly initial: string;
  readonly states: Readonly<Record<string, StateSpec>>;
  readonly offers?: Offers;
  readonly on: Readonly<Record<string, readonly TransitionSpec[]>>;
  readonly invariants: Conditions<unknown>;
  readonly resolve?: (args: unknown) => unknown;
  readonly requires?: Conditions<unknown>;
  readonly ensures?: Conditions<unknown>;
}

export type Events = Readonly<Record<string, AnyEvent>>;

interface Chart extends ChartSpec {
  readonly service: ServiceDefinition;
  readonly description: string;
}

export interface Machine extends Chart {
  readonly kind: "machine";
}

/**
 * A UI element that the user operates. The implementation decides how the user operates it, for example by a tap or a
 * swipe.
 */
export interface Control<P extends Shape = Shape> {
  /**
   * The name a user sees or hears for the control: the visible text, or for an element without text, the name a screen
   * reader reads. The implementation's element has this accessible name. When the control is drawn as one element per
   * payload, every element has this name, and the element's value tells the payloads apart.
   */
  readonly label: string;
  readonly payload?: P;
}

// biome-ignore lint/suspicious/noExplicitAny: a control of any payload
export type AnyControl = Control<any>;

type Controls = Readonly<Record<string, AnyControl>>;

export interface Screen<I extends Shape = Shape, O extends Shape = Shape, Cs extends Controls = Controls>
  extends Chart {
  readonly kind: "screen";
  readonly input: I;
  readonly output: O;
  readonly controls: Cs;
}

// biome-ignore lint/suspicious/noExplicitAny: a screen of any shape
export type AnyScreen = Screen<any, any, any>;

/** A contract: its members without `states`, its start states, and the object that `contract()` returned. */
export interface Contract {
  readonly service: string;
  readonly place: Place;
  readonly members: Readonly<Record<string, unknown>>;
  readonly states: Readonly<Record<string, readonly unknown[]>>;
  readonly value: object;
}

export type Services = ReadonlyMap<string, { readonly definition: ServiceDefinition }>;
