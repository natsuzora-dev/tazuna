const written = new WeakMap<object, readonly object[]>();

/**
 * Returns `definition`, keeping `options`, the objects written to the definer calls that made it, before defaults fill
 * them in. `check` reads the form of the spec from them.
 */
export function withWritten<T extends object>(definition: T, ...options: readonly object[]): T {
  written.set(definition, options);
  return definition;
}

/** The objects written to the definer calls that made `definition`, in call order. */
export const writtenOptions = (definition: object): readonly object[] => written.get(definition) ?? [];
