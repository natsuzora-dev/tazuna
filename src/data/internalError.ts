/**
 * A state that the types or check rule out, so a tazuna bug and never the author's: the run stops on it, also inside
 * author code, where any other throw is the author's.
 */
export class InternalError extends Error {}

/** Lean's expectFound, with an InternalError where Lean notes a bug. */
export function expectFound<T>(what: string, found: T | undefined): T {
  if (found === undefined) throw new InternalError(`no ${what}`);
  return found;
}
