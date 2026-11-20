/**
 * The options of a search. The inputs appended to the start are at most `bound`. `step` gives the result of a path from
 * its parent's result and its last input. `next` lists the inputs enabled after `path`. `merge` either names the state
 * after a path by `fingerprint`, so that a path reaching a visited state is not extended, or is "none", so that every
 * path is extended.
 */
export interface SearchOptions<I, R> {
  readonly start: { readonly path: readonly I[]; readonly result: R };
  readonly bound: number;
  readonly step: (parent: R, input: I) => R;
  readonly next: (path: readonly I[], result: R) => readonly I[];
  readonly merge: { readonly fingerprint: (result: R) => string } | "none";
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
  const visited = new Set<string>();
  // A taken entry is cleared, so that a parent's result is kept only while its children wait.
  const queue: ({ readonly path: readonly I[]; readonly parent: R; readonly input: I } | undefined)[] = [];
  const extend = (path: readonly I[], result: R): void => {
    if (path.length - start.path.length >= bound) return;
    if (merge !== "none") {
      const state = merge.fingerprint(result);
      if (visited.has(state)) return;
      visited.add(state);
    }
    for (const input of next(path, result)) queue.push({ path: [...path, input], parent: result, input });
  };
  yield start;
  extend(start.path, start.result);
  for (let i = 0; i < queue.length; i += 1) {
    const { path, parent, input } = queue[i] as NonNullable<(typeof queue)[number]>;
    queue[i] = undefined;
    const result = step(parent, input);
    yield { path, result, parent };
    extend(path, result);
  }
}
