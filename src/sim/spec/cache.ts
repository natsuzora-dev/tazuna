import type { InstanceId } from "../../service/instance.ts";

/**
 * A cached evaluation. `versions` holds the names that make the evaluation stale, with their write counts at evaluation
 * time.
 */
interface Evaluation {
  readonly versions: ReadonlyMap<string, number>;
  readonly reads: readonly string[];
}

/**
 * The evaluation cache: the write count of each value name, the reads of the evaluations it tracks, and the
 * evaluations of each instance (its always transitions, and the items of each map state).
 */
export class Cache {
  /** An evaluation cached at older write counts is stale. */
  private readonly versions = new Map<string, number>();
  private readonly tracked: Set<string>[] = [];
  private quietDepth = 0;
  private readonly evaluations = new Map<InstanceId, Map<string, Evaluation>>();

  clone(): Cache {
    const copy = new Cache();
    for (const [name, version] of this.versions) copy.versions.set(name, version);
    for (const [id, byPart] of this.evaluations) copy.evaluations.set(id, new Map(byPart));
    return copy;
  }

  /**
   * Whether the current read is inside `quietly`, where no read counts: neither the evaluations being tracked nor the
   * instrumentation see it.
   */
  get quiet(): boolean {
    return this.quietDepth > 0;
  }

  read(name: string): void {
    for (const t of this.tracked) t.add(name);
  }

  wrote(name: string): void {
    this.versions.set(name, this.version(name) + 1);
  }

  /** Returns the names that `f` reads, in first-read order. */
  track(f: () => void): string[] {
    const reads = new Set<string>();
    this.tracked.push(reads);
    try {
      f();
    } finally {
      this.tracked.pop();
    }
    return [...reads];
  }

  quietly<T>(f: () => T): T {
    this.quietDepth += 1;
    try {
      return f();
    } finally {
      this.quietDepth -= 1;
    }
  }

  /** Remembers an evaluation; `watched` are kept with the write counts that they have now. */
  remember(id: InstanceId, part: string, reads: readonly string[], watched: readonly string[]): void {
    const byPart = this.evaluations.get(id) ?? new Map<string, Evaluation>();
    this.evaluations.set(id, byPart);
    byPart.set(part, { versions: new Map(watched.map((name) => [name, this.version(name)])), reads });
  }

  /** Returns the reads of the evaluation while none of its watched names has been written since it was remembered. */
  freshReads(id: InstanceId, part: string): readonly string[] | undefined {
    const evaluation = this.evaluations.get(id)?.get(part);
    if (evaluation === undefined || ![...evaluation.versions].every(([name, v]) => this.version(name) === v))
      return undefined;
    return evaluation.reads;
  }

  private version(name: string): number {
    return this.versions.get(name) ?? 0;
  }
}

/** The plain method that the cache must agree with: no evaluation is ever fresh, so each one runs again. */
export class NoCache extends Cache {
  override freshReads(): undefined {
    return undefined;
  }
}
