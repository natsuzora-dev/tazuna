import { orderFree } from "./canonical.ts";
import { canonicalJson } from "./values.ts";

export class Subscriptions<T> {
  private readonly open = new Map<string, { readonly value: T; last?: string }>();

  clone(copy: (value: T) => T): Subscriptions<T> {
    const cloned = new Subscriptions<T>();
    for (const [id, { value, last }] of this.open)
      cloned.open.set(id, { value: copy(value), ...(last === undefined ? {} : { last }) });
    return cloned;
  }

  /** Returns false when a subscription with the id is already open. */
  subscribe(id: string, value: T): boolean {
    if (this.open.has(id)) return false;
    this.open.set(id, { value });
    return true;
  }

  unsubscribe(id: string): boolean {
    return this.open.delete(id);
  }

  get(id: string): T | undefined {
    return this.open.get(id)?.value;
  }

  entries(): [string, T][] {
    return [...this.open].map(([id, { value }]) => [id, value]);
  }

  fingerprint(of: (value: T) => unknown): unknown {
    return [...this.open].map(([id, { value, last }]) => [id, of(value), last ?? null]);
  }

  /**
   * Returns whether `answer`, bagged or order-free, repeats the previous answer, and records it as the latest
   * otherwise. An answer to a subscription that is not open never repeats.
   */
  repeats(id: string, answer: unknown): boolean {
    const open = this.open.get(id);
    if (open === undefined) return false;
    const text = canonicalJson(orderFree(answer));
    if (text === open.last) return true;
    open.last = text;
    return false;
  }
}
