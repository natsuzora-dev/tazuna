import type { z } from "zod";

export type Collection =
  | { readonly kind: "bag" }
  | { readonly kind: "set" }
  | { readonly kind: "sortedBy"; readonly key: string };

/**
 * The collection of each marked array, keyed by a check rather than by the schema, because Zod copies checks into the
 * schemas that `.min()` and similar methods return.
 */
const collections = new WeakMap<object, Collection>();

export const mark = (check: z.core.$ZodCheck<never>, collection: Collection): void => {
  collections.set(check, collection);
};

export const markOf = (check: z.core.$ZodCheck<never>): Collection | undefined => collections.get(check);

export const collectionOf = (schema: z.core.$ZodType): Collection | undefined =>
  (schema._zod.def.checks ?? []).map((c) => collections.get(c)).find((c) => c !== undefined);
