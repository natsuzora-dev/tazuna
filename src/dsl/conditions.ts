/** Named conditions. A name appears in rejection reasons and violation data. */
export type Conditions<Args> = Readonly<Record<string, (args: Args) => boolean>>;
export type Named<N extends string, Args> = { readonly [K in N]: (args: Args) => boolean };
/** The type of a keyword whose values another type parameter infers. */
export type Present<N extends string> = { readonly [K in N]: unknown };

/** Returns the name of the first condition that fails, and builds the arguments only when there is a condition. */
export function firstFailing<Args>(conditions: Conditions<Args> | undefined, args: () => Args): string | undefined {
  const entries = Object.entries(conditions ?? {});
  if (entries.length === 0) return undefined;
  const built = args();
  for (const [name, condition] of entries) if (!condition(built)) return name;
  return undefined;
}
