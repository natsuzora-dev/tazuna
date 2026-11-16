import { BagValue } from "../../data/bag.ts";
import type { Fields } from "../../data/values.ts";
import type { AnyEntity } from "../../dsl/entity.ts";
import type { RecordSource } from "../../service/records.ts";

/**
 * Returns a view of the records that reads each value from `source`. Read granularity: get(key) reads existence; size,
 * filter and the other Bag methods read the key set; a field access reads that field; enumerating field names (spread)
 * reads every field. Field names come from the entity definition and are not reads. A table calls spec functions on its
 * records in the order of the source's keys.
 */
export function recordsView(
  entities: Readonly<Record<string, AnyEntity>>,
  source: RecordSource,
): Record<string, unknown> {
  const row = (entity: string, key: string | undefined, names: readonly string[]): Fields => {
    const target: Fields = {};
    const fetch = (p: string | symbol): boolean => {
      if (typeof p !== "string" || !names.includes(p)) return false;
      target[p] = source.field(entity, key, p);
      return true;
    };
    return new Proxy(target, {
      get: (t, p, r) => {
        fetch(p);
        return Reflect.get(t, p, r);
      },
      has: (_, p) => fetch(p),
      ownKeys: (t) => {
        for (const n of names) fetch(n);
        return Reflect.ownKeys(t);
      },
      getOwnPropertyDescriptor: (t, p) => {
        fetch(p);
        return Reflect.getOwnPropertyDescriptor(t, p);
      },
    });
  };
  const table = (entity: string, names: readonly string[]): unknown => {
    const rows = new Map<string, Fields>();
    const rowOf = (key: string) => {
      const known = rows.get(key) ?? row(entity, key, names);
      rows.set(key, known);
      return known;
    };
    const get = (key: unknown) => (source.exists(entity, String(key)) ? rowOf(String(key)) : undefined);
    return Object.assign(new BagValue(() => source.keys(entity).map(rowOf)), { get });
  };
  return Object.fromEntries(
    Object.entries(entities).map(([name, entity]) => {
      const names = Object.keys(entity.fields);
      return [name, entity.single ? row(name, undefined, names) : table(name, names)];
    }),
  );
}
