/**
 * Lean's InstanceId: an instance of a machine or screen, or a copy of a map state. `serial` numbers the instances of
 * `chart` in creation order from 0. A copy is the copy of `owner`'s map state `map` for the item whose key has the
 * canonical JSON `key`. Ids are interned, so equal ids are the same object and key maps and sets as they are.
 */
export type InstanceId =
  | { readonly kind: "top"; readonly chart: string; readonly serial: number }
  | { readonly kind: "copy"; readonly owner: InstanceId; readonly map: string; readonly key: string };

const interned = new Map<string, InstanceId>();
const names = new WeakMap<InstanceId, string>();

function intern(id: InstanceId): InstanceId {
  const name = JSON.stringify(id);
  const found = interned.get(name);
  if (found !== undefined) return found;
  interned.set(name, id);
  names.set(id, name);
  return id;
}

/** The JSON of an id, for the one string form of a ValueKey. */
export const instanceName = (id: InstanceId): string => names.get(id) as string;

export const topId = (chart: string, serial = 0): InstanceId => intern({ kind: "top", chart, serial });

export const copyId = (owner: InstanceId, map: string, key: string): InstanceId =>
  intern({ kind: "copy", owner, map, key });

export const chartOf = (id: InstanceId): string => (id.kind === "top" ? id.chart : chartOf(id.owner));

export const serialOf = (id: InstanceId): number => (id.kind === "top" ? id.serial : serialOf(id.owner));

/** The instance itself, or the owner of a copy. */
export const ownerId = (id: InstanceId): InstanceId => (id.kind === "copy" ? id.owner : id);

/** Lean's InstanceId.within: whether `i` is `r` or a copy of `r`. */
export const within = (i: InstanceId, r: InstanceId): boolean => i === r || ownerId(i) === r;
