import type { Obligation } from "../../data/uncovered.ts";
import { canonicalJson } from "../../data/values.ts";

export class Coverage {
  private readonly reached = new Set<string>();

  clone(): Coverage {
    const copy = new Coverage();
    copy.addAll(this);
    return copy;
  }

  /** Adds what `other` reached and `before`, when given, had not. */
  addAll(other: Coverage, before?: Coverage): void {
    for (const key of other.reached) if (before?.reached.has(key) !== true) this.reached.add(key);
  }

  reach(obligation: Obligation): void {
    this.reached.add(canonicalJson(obligation));
  }

  /** The canonical JSON of each reached obligation, sorted. */
  keys(): string[] {
    return [...this.reached].sort();
  }

  has(obligation: Obligation): boolean {
    return this.reached.has(canonicalJson(obligation));
  }
}
