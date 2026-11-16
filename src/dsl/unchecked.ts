/**
 * Passes a value through the type check unchanged. A spec or scenario file uses it to write, on purpose, a value that its
 * type rejects, because such a file has no type assertion (Restricted.as).
 */
export function unchecked(value: unknown): never {
  return value as never;
}
