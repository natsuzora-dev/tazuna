import type { Obligation } from "../data/uncovered.ts";
import { canonicalJson } from "../data/values.ts";

export class Coverage {
  private readonly reached = new Set<string>();

  clone(): Coverage {
    const copy = new Coverage();
    copy.addAll(this);
    return copy;
  }

  addAll(other: Coverage): void {
    for (const key of other.reached) this.reached.add(key);
  }

  reach(obligation: Obligation): void {
    this.reached.add(canonicalJson(obligation));
  }

  has(obligation: Obligation): boolean {
    return this.reached.has(canonicalJson(obligation));
  }
}
