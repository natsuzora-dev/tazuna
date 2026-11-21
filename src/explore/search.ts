import { hash } from "node:crypto";

/**
 * The visited set of a search: a 64-bit hash of each fingerprint instead of its text, as TLC keeps. Two fingerprints
 * with the same hash count as one, which `collisionProbability` bounds.
 */
export class Visited {
  private readonly hashes = new Set<bigint>();

  /** Adds `fingerprint`, and returns false when its hash was already visited. */
  add(fingerprint: string): boolean {
    const h = hash("sha256", fingerprint, "buffer").readBigUInt64LE(0);
    if (this.hashes.has(h)) return false;
    this.hashes.add(h);
    return true;
  }

  get size(): number {
    return this.hashes.size;
  }
}

/** The probability that two fingerprints in some visited set of `sizes` share a hash, if the hash acts at random. */
export const collisionProbability = (sizes: readonly number[]): number =>
  sizes.reduce((p, n) => p + (n * (n - 1)) / 2 / 2 ** 64, 0);

/**
 * The options of a search. The inputs appended to the start are at most `bound`. `next` lists the inputs that may follow
 * `path`, and `step` gives the result of `path` from its parent's result, or undefined when its last input does not
 * follow after all, which Lean's Space.next leaves out. `merge` either names the state after a path by `fingerprint`
 * and adds it to `visited`, so that a path reaching a visited state is not extended, or is "none", so that every path
 * is extended.
 */
export interface SearchOptions<I, R> {
  readonly start: { readonly path: readonly I[]; readonly result: R };
  readonly bound: number;
  readonly step: (parent: R, path: readonly I[]) => R | undefined;
  readonly next: (path: readonly I[], result: R) => readonly I[];
  readonly merge: { readonly fingerprint: (result: R) => string; readonly visited: Visited } | "none";
}

/**
 * Searches breadth-first, continuing each path from its parent's result, with a visited set of state fingerprints.
 * Yields each path with its result and its parent's result (none for the start); the caller stops the search by
 * leaving the loop. Lean's Space.merged, whose layers the queue takes in order.
 */
export function* search<I, R>(
  options: SearchOptions<I, R>,
): Generator<{ readonly path: readonly I[]; readonly result: R; readonly parent?: R }> {
  const { start, bound, step, next, merge } = options;
  // A taken entry is cleared, so that a parent's result is kept only while its children wait.
  const queue: ({ readonly path: readonly I[]; readonly parent: R } | undefined)[] = [];
  const extend = (path: readonly I[], result: R): void => {
    if (path.length - start.path.length >= bound) return;
    if (merge !== "none" && !merge.visited.add(merge.fingerprint(result))) return;
    for (const input of next(path, result)) queue.push({ path: [...path, input], parent: result });
  };
  yield start;
  extend(start.path, start.result);
  for (let i = 0; i < queue.length; i += 1) {
    const { path, parent } = queue[i] as NonNullable<(typeof queue)[number]>;
    queue[i] = undefined;
    const result = step(parent, path);
    if (result === undefined) continue;
    yield { path, result, parent };
    extend(path, result);
  }
}
