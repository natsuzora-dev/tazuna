import type { InstanceId } from "../data/step.generated.ts";
import type { Json } from "../data/values.ts";

export type { InstanceId };

/*
 * Ids are interned, so equal ids are the same object and key maps and sets as they are. The table holds them weakly,
 * so it does not grow across runs.
 */
const interned = new Map<string, WeakRef<InstanceId>>();
const released = new FinalizationRegistry<string>((name) => {
  if (interned.get(name)?.deref() === undefined) interned.delete(name);
});
const names = new WeakMap<InstanceId, string>();

function intern(id: InstanceId): InstanceId {
  const name = JSON.stringify(id);
  const found = interned.get(name)?.deref();
  if (found !== undefined) return found;
  interned.set(name, new WeakRef(id));
  released.register(id, name);
  names.set(id, name);
  return id;
}

/** The JSON of an id, for the one string form of a ValueKey. */
export const instanceName = (id: InstanceId): string => names.get(id) as string;

export const topId = (chart: string): InstanceId => intern({ kind: "top", chart });

/** The `nth` opening of the screen `chart` by the `opens` of `opener` at state `state` and key `key`. */
export const openedId = (chart: string, opener: InstanceId, state: string, key: string, nth: number): InstanceId =>
  intern({ kind: "opened", chart, opener, state, key, nth });

/** The copy of `owner`'s map state `map` for the item key whose canonical JSON is `canonicalKey`. */
export const copyId = (owner: InstanceId, map: string, canonicalKey: string): InstanceId =>
  intern({ kind: "copy", owner, map, key: JSON.parse(canonicalKey) as Json });

export const chartOf = (id: InstanceId): string => (id.kind === "copy" ? chartOf(id.owner) : id.chart);

/** The instance itself, or the owner of a copy. */
export const ownerId = (id: InstanceId): InstanceId => (id.kind === "copy" ? id.owner : id);

/** The map state of a copy. */
export const mapOf = (id: InstanceId): string | undefined => (id.kind === "copy" ? id.map : undefined);

/** Lean's InstanceId.within: whether `i` is `r` or a copy of `r`. */
export const within = (i: InstanceId, r: InstanceId): boolean => i === r || ownerId(i) === r;
