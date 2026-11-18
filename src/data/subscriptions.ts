import { orderFree } from "./canonical.ts";
import { canonicalJson } from "./values.ts";

/** The open subscriptions by id; `key` turns an id into a map key. */
export class Subscriptions<I, T> {
  private readonly open = new Map<string, { readonly id: I; readonly value: T; last?: string }>();

  private readonly key: (id: I) => string;

  constructor(key: (id: I) => string) {
    this.key = key;
  }

  clone(copy: (value: T) => T): Subscriptions<I, T> {
    const cloned = new Subscriptions<I, T>(this.key);
    for (const [k, { id, value, last }] of this.open)
      cloned.open.set(k, { id, value: copy(value), ...(last === undefined ? {} : { last }) });
    return cloned;
  }

  /** Returns false when a subscription with the id is already open. */
  subscribe(id: I, value: T): boolean {
    if (this.open.has(this.key(id))) return false;
    this.open.set(this.key(id), { id, value });
    return true;
  }

  unsubscribe(id: I): boolean {
    return this.open.delete(this.key(id));
  }

  get(id: I): T | undefined {
    return this.open.get(this.key(id))?.value;
  }

  entries(): [I, T][] {
    return [...this.open.values()].map(({ id, value }) => [id, value]);
  }

  fingerprint(of: (value: T) => unknown): unknown {
    return [...this.open].map(([k, { value, last }]) => [k, of(value), last ?? null]);
  }

  /**
   * Returns whether `answer`, bagged or order-free, repeats the previous answer, and records it as the latest
   * otherwise. An answer to a subscription that is not open never repeats.
   */
  repeats(id: I, answer: unknown): boolean {
    const open = this.open.get(this.key(id));
    if (open === undefined) return false;
    const text = canonicalJson(orderFree(answer));
    if (text === open.last) return true;
    open.last = text;
    return false;
  }
}
