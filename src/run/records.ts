import type { Fields } from "../data/values.ts";
import type { AnyEntity } from "../dsl/entity.ts";
import type { RecordSource } from "../semantics/service/records.ts";

/**
 * Returns a view of the records that reads each value from `source`. Read granularity: get(key) reads existence;
 * length, elements, filter and the like read the key set; a field access reads that field; enumerating field names
 * (spread) reads every field. Field names come from the entity definition and are not reads. Table elements are in the
 * order of the source's keys.
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
    const target: Fields[] & { get?: (key: unknown) => Fields | undefined } = [];
    target.get = (key: unknown) => (source.exists(entity, String(key)) ? rowOf(String(key)) : undefined);
    const filled = () => {
      const keys = source.keys(entity);
      if (target.length === 0) target.push(...keys.map(rowOf));
    };
    return new Proxy(target, {
      get: (t, p, r) => {
        if (p !== "get") filled();
        return Reflect.get(t, p, r);
      },
      has: (t, p) => {
        filled();
        return Reflect.has(t, p);
      },
      ownKeys: (t) => {
        filled();
        return Reflect.ownKeys(t);
      },
    });
  };
  return Object.fromEntries(
    Object.entries(entities).map(([name, entity]) => {
      const names = Object.keys(entity.fields);
      return [name, entity.single ? row(name, undefined, names) : table(name, names)];
    }),
  );
}
