import type { z } from "zod";
import type { Made } from "../data/bag.ts";
import type { Shape } from "../data/values.ts";
import type { ChartSpec, StateSpec } from "./definition.ts";
import type { DefaultedShape, Immutable, Row } from "./entity.ts";

type TreeNode =
  | {
      /**
       * The kind of the state, none for an atomic or compound state. Children are separate states when they react to
       * messages differently (`on`, `after`, `always`, or the requests sent on entry). When only a value differs, the
       * value is in context.
       */
      readonly type?: never;
      /**
       * The shapes of the values that the state holds. The body writes each value's expression in `holds`, and
       * expressions read the values as `held`.
       */
      readonly held?: Shape;
      readonly initial?: string;
      /** The child states, whose names are unique in the tree. */
      readonly states?: Tree;
    }
  | { readonly type: "parallel"; readonly held?: Shape; readonly initial?: never; readonly states: Tree }
  | {
      readonly type: "map";
      /**
       * The shape of a copy's key. Expressions in a copy read it as `key`, and `active` outside the map state does not
       * name a copy's states.
       */
      readonly key: Shape;
      /**
       * The context fields of each copy. In a copy, `context` has these fields and the instance's fields, whose names
       * differ (`duplicateContextFields`). `assign` writes each field where it is kept.
       */
      readonly context?: DefaultedShape;
      readonly held?: never;
      readonly initial?: string;
      readonly states: Tree;
    }
  | { readonly type: "final" | "history"; readonly held?: never; readonly initial?: never; readonly states?: never };
export type Tree = { readonly [name: string]: TreeNode };

type CheckNode<T> = T extends { readonly type: "parallel"; readonly states: infer C }
  ? { readonly states: CheckTree<C> }
  : T extends { readonly states: infer C }
    ? { readonly initial: keyof C & string; readonly states: CheckTree<C> }
    : { readonly initial?: never };
export type CheckTree<T> = { readonly [K in keyof T]: CheckNode<T[K]> };

type Empty = Record<never, never>;
type Simplify<T> = { readonly [K in keyof T]: T[K] };
// biome-ignore lint/suspicious/noEmptyInterface: a named type for error messages
interface NoHeld {}
type HeldRow<T> = [keyof T] extends [never] ? NoHeld : Simplify<T>;
type OwnShape<T> = T extends { readonly held: infer H extends Shape } ? H : Empty;
type OwnRow<T> = T extends { readonly held: infer H extends Shape } ? Row<H> : Empty;
type Kind<T> = T extends { readonly type: "history" }
  ? "history"
  : T extends { readonly type: "final" }
    ? "final"
    : T extends { readonly type: "map" }
      ? "map"
      : T extends { readonly states: Tree }
        ? "parent"
        : "atomic";
interface CopyOf<Key, Ctx> {
  readonly key: Key;
  readonly context: Ctx;
}
type CopyOfNode<T> = T extends { readonly type: "map"; readonly key: infer Key extends Shape }
  ? CopyOf<Key, T extends { readonly context: infer C extends DefaultedShape } ? C : Empty>
  : never;

/**
 * An entry of the flattened tree. `path` keeps two states of one name apart, so that Duplicates finds them. `map` is
 * the nearest map state above. `regionOrMap` is, walking up from the state itself, the first child of a parallel state
 * or the first map state strictly above, or null when there is neither.
 */
interface Entry<K, Own extends Shape, Held, Above, Kd, Path, M, Cp, RegionOrMap> {
  readonly name: K;
  readonly path: Path;
  readonly own: Own;
  readonly above: Above;
  readonly held: HeldRow<Above & Held>;
  readonly kind: Kd;
  readonly map: M;
  readonly copyShape: Cp;
  readonly regionOrMap: RegionOrMap;
}
type Entries<T, Above, Path extends string, M, RegionOrMap, InParallel> = {
  [K in keyof T & string]:
    | Entry<
        K,
        OwnShape<T[K]>,
        OwnRow<T[K]>,
        Above,
        Kind<T[K]>,
        Path,
        M,
        CopyOfNode<T[K]>,
        InParallel extends true ? K : RegionOrMap
      >
    | (T[K] extends { readonly states: infer C }
        ? Entries<
            C,
            Above & OwnRow<T[K]>,
            `${Path}/${K}`,
            T[K] extends { readonly type: "map" } ? K : M,
            T[K] extends { readonly type: "map" } ? K : InParallel extends true ? K : RegionOrMap,
            T[K] extends { readonly type: "parallel" } ? true : false
          >
        : never);
}[keyof T & string];
type AnyEntry = Entry<string, Shape, unknown, unknown, string, string, unknown, unknown, string | null>;

type FlatEntries<T> = Entries<T, Empty, "", never, null, false>;
export type Flat<T> = { readonly [E in FlatEntries<T> as E["name"]]: E };
type Names<T> = keyof Flat<T> & string;

export type IsUnion<U, A = U> = U extends unknown ? ([A] extends [U] ? false : true) : never;
type Duplicates<T> = {
  [K in Names<T>]: true extends IsUnion<Extract<FlatEntries<T>, { readonly name: K }>> ? K : never;
}[Names<T>];
type Shadowed<F> = {
  [K in keyof F & string]: F[K] extends AnyEntry
    ? `${K}.${Extract<keyof F[K]["own"], keyof F[K]["above"]> & string}`
    : never;
}[keyof F & string];
type Nullable<F> = {
  [K in keyof F & string]: F[K] extends AnyEntry
    ? {
        [h in keyof F[K]["own"] & string]: null extends z.output<F[K]["own"][h]>
          ? `${K}.${h}`
          : undefined extends z.output<F[K]["own"][h]>
            ? `${K}.${h}`
            : never;
      }[keyof F[K]["own"] & string]
    : never;
}[keyof F & string];
type InMap<F, Kinds> = {
  [K in keyof F]: F[K] extends AnyEntry
    ? [F[K]["map"]] extends [never]
      ? never
      : F[K]["kind"] extends Kinds
        ? K
        : never
    : never;
}[keyof F];
export type ErrorIf<Name extends string, V> = [V] extends [never] ? unknown : { readonly [k in Name]: V };
export type TreeErrors<T> = ErrorIf<"duplicateStateNames", Duplicates<T>> &
  ErrorIf<"shadowedHeld", Shadowed<Flat<T>>> &
  ErrorIf<"nullableHeld", Nullable<Flat<T>>> &
  ErrorIf<"nestedMap", `${InMap<Flat<T>, "map"> & string}: a copy would read two keys as key`> &
  ErrorIf<"finalInMap", `${InMap<Flat<T>, "final"> & string}: a copy ends only when its key leaves items`>;

export type HeldIn<F, K extends keyof F> = F[K] extends AnyEntry ? F[K]["held"] : never;
export type KindOf<F, K extends keyof F> = F[K] extends AnyEntry ? F[K]["kind"] : never;
export type MapOf<F, K extends keyof F> = F[K] extends AnyEntry ? F[K]["map"] : never;
/** The states outside every map state's copies, map states included. */
export type OuterNames<F> = { [K in keyof F]: [MapOf<F, K>] extends [never] ? K : never }[keyof F] & string;
type InRegionOrMap<E, RegionOrMap extends string> = E extends AnyEntry
  ? E["name"] extends RegionOrMap
    ? true
    : `${E["path"]}/` extends `${string}/${RegionOrMap}/${string}`
      ? true
      : false
  : never;
/** The states of `N` outside the region or map state that holds the state `K`. */
export type OutsideRegionOrMap<F, K extends keyof F, N extends keyof F & string> = F[K] extends {
  readonly regionOrMap: null;
}
  ? never
  : F[K] extends { readonly regionOrMap: infer RegionOrMap extends string }
    ? { [S in N]: InRegionOrMap<F[S], RegionOrMap> extends true ? never : S }[N]
    : never;
export type CopyNames<F, M> = {
  [K in keyof F]: [MapOf<F, K>] extends [never] ? never : MapOf<F, K> extends M ? K : never;
}[keyof F] &
  string;
type MapNames<F> = { [K in keyof F]: KindOf<F, K> extends "map" ? K : never }[keyof F] & string;
type CopyIn<F, M> = M extends keyof F ? (F[M] extends AnyEntry ? F[M]["copyShape"] : never) : never;
export type CopyKey<F, M> = CopyIn<F, M> extends CopyOf<infer Key extends Shape, unknown> ? Row<Key> : never;
export type CopyContext<F, M> = CopyIn<F, M> extends CopyOf<unknown, infer C extends DefaultedShape> ? C : Empty;
export type SharedContextFields<F, Ctx> = {
  [M in MapNames<F>]: Extract<keyof CopyContext<F, M>, keyof Ctx>;
}[MapNames<F>];
type OwnOf<F, K extends keyof F> = F[K] extends AnyEntry ? F[K]["own"] : never;
type HasHeld<F, K extends keyof F> = keyof OwnOf<F, K> extends never ? false : true;

export type TableKeys<F> = { [K in keyof F]: KindOf<F, K> extends "history" ? never : K }[keyof F];
type HeldKeys<F> = { [K in keyof F]: HasHeld<F, K> extends true ? K : never }[keyof F];
type TableRow<F, K extends keyof F, A, B> =
  HasHeld<F, K> extends true
    ? B & {
        /** The expressions of the held values, which do not read `held`. */
        readonly holds: Holds<A, OwnOf<F, K>>;
      }
    : B & { readonly holds?: never };
type Holds<A, Own extends Shape> = {
  readonly [h in keyof Own]: (args: A) => Made<Immutable<z.output<Own[h]>>> | null | undefined;
};
/**
 * The behaviors of the states. A state without behavior is left out (`NonCanonical.emptyKeyword`). A state with held values needs `holds`
 * (`missingHolds`), and a map state needs `items` (`missingItems`).
 */
export type Table<
  F,
  K extends keyof F,
  A extends { readonly [K in keyof F]: unknown },
  Behavior extends { readonly [K in keyof F]: unknown },
> = {
  readonly [P in K]?: TableRow<F, P, A[P], Behavior[P]>;
};
export type RowsWritten<F, K> = ErrorIf<"missingHolds", Exclude<HeldKeys<F>, K>> &
  ErrorIf<"missingItems", Exclude<MapNames<F>, K>>;

type RuntimeNode = {
  readonly type?: string;
  readonly key?: Shape;
  readonly context?: Shape;
  readonly held?: Shape;
  readonly initial?: string;
  readonly states?: Readonly<Record<string, RuntimeNode>>;
};
type Assembled = Required<Pick<ChartSpec, "states" | "held" | "holds">>;

export function assemble(tree: object, table: object): Assembled {
  const held: Record<string, Shape> = {};
  const holds: Record<string, NonNullable<ChartSpec["holds"]>[string]> = {};
  const behaviors = table as Readonly<Record<string, { readonly holds?: NonNullable<ChartSpec["holds"]>[string] }>>;
  const nest = (nodes: Readonly<Record<string, RuntimeNode>>): Record<string, StateSpec> =>
    Object.fromEntries(
      Object.entries(nodes).map(([name, node]) => {
        const { holds: own, ...behavior } = behaviors[name] ?? {};
        if (node.held !== undefined) held[name] = node.held;
        if (own !== undefined) holds[name] = own;
        const spec = {
          ...(node.type === undefined ? {} : { type: node.type }),
          ...(node.key === undefined ? {} : { key: node.key }),
          ...(node.context === undefined ? {} : { context: node.context }),
          ...(node.initial === undefined ? {} : { initial: node.initial }),
          ...(node.states === undefined ? {} : { states: nest(node.states) }),
          ...behavior,
        };
        return [name, spec as StateSpec];
      }),
    );
  return { states: nest(tree as Readonly<Record<string, RuntimeNode>>), held, holds };
}
