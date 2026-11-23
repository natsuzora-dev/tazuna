/** Named conditions. A name appears in rejection reasons and violation data. */
export type Conditions<Args> = Readonly<Record<string, (args: Args) => boolean>>;
export type Named<N extends string, Args> = { readonly [K in N]: (args: Args) => boolean };
/** The type of a keyword whose values another type parameter infers. */
export type Present<N extends string> = { readonly [K in N]: unknown };
/** The time of the message in progress, or of the state that an invariant checks, in milliseconds since the epoch. */
export interface Now {
  readonly now: number;
}
