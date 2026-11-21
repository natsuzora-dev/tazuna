import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Fault } from "../data/fault.generated.ts";
import type { Fields } from "../data/values.ts";
import { type Located, withExtra } from "../data/violation.ts";
import { schemaOwner } from "../spec/structure.ts";
import { changeOf, ref, type Service, uniqueOf } from "./basic.ts";
import { Failed, issueViolation } from "./functions.ts";
import type { Emitted } from "./message.ts";
import { type Records, type Row, recordSource } from "./records.ts";
import type { Run } from "./state.ts";

type Written = {
  rows: Map<string, string[]>;
  /** For each entity, the keys of the records created again with an existing key and not deleted since. */
  duplicated: Map<string, Set<string>>;
};

function uniqueTaken(r: Run, written: ReadonlyMap<string, readonly string[]>): boolean {
  let taken = false;
  for (const [name, keys] of written) {
    const unique = uniqueOf(r.st, name);
    const rows = r.state.records.keyed.get(name) ?? new Map<string, Row>();
    const uniqueValue = (row: Row) => JSON.stringify(Object.fromEntries(unique.map((f) => [f, row.encoded[f]])));
    for (const key of keys) {
      const row = rows.get(key);
      if (row === undefined || unique.length === 0 || unique.some((f) => row.value[f] === null)) continue;
      r.note.readRecord({ entity: name });
      for (const k of rows.keys())
        if (k !== key) for (const field of unique) r.note.readRecord({ entity: name, key: k, field });
      for (const [k, other] of rows) if (k !== key && uniqueValue(other) === uniqueValue(row)) taken = true;
    }
  }
  return taken;
}

/** Returns the record that an event writes, as its entity and its key (none for a single entity). */
export function writtenRecord(
  st: Service,
  { emit: emitted }: Encoded,
): { readonly entity: string; readonly key?: string } | undefined {
  const change = changeOf(st, emitted.event);
  if (change === undefined || change.kind === "none") return undefined;
  return change.kind === "set"
    ? { entity: change.entity }
    : { entity: change.entity, key: String(emitted.payload[change.key]) };
}

function apply(r: Run, { emit: emitted, encoded }: Encoded, written: Written): void {
  const change = changeOf(r.st, emitted.event);
  if (change === undefined || change.kind === "none") return;
  const records = r.state.records;
  const payload = emitted.payload;
  if (change.kind === "set") {
    for (const field of change.writes) r.note.wroteRecord({ entity: change.entity, field }, false);
    const old = records.singles.get(change.entity);
    records.singles.set(change.entity, {
      value: { ...old?.value, ...payload },
      encoded: { ...old?.encoded, ...encoded },
    });
    return;
  }
  const name = change.entity;
  const rows = records.keyed.get(name);
  if (rows === undefined) return;
  const key = String(payload[change.key]);
  if (change.kind === "update")
    for (const field of change.writes) r.note.wroteRecord({ entity: name, key, field }, false);
  else {
    r.note.wroteRecord({ entity: name }, true);
    r.note.wroteRecord({ entity: name, key }, false);
    for (const field of change.fields) r.note.wroteRecord({ entity: name, key, field }, false);
  }
  const keys = written.rows.get(name) ?? [];
  written.rows.set(name, keys);
  if (change.kind === "delete") {
    rows.delete(key);
    written.duplicated.get(name)?.delete(key);
    return;
  }
  if (change.kind === "create" && rows.has(key)) {
    const again = written.duplicated.get(name) ?? new Set<string>();
    written.duplicated.set(name, again.add(key));
  }
  if (!keys.includes(key)) keys.push(key);
  const old = change.kind === "create" ? undefined : rows.get(key);
  rows.set(key, { value: { ...old?.value, ...payload }, encoded: { ...old?.encoded, ...encoded } });
}

/** An emitted event with its payload as encoded. */
export interface Encoded {
  readonly emit: Emitted;
  readonly encoded: Fields;
}

export function applyAll(r: Run, events: readonly Encoded[]): "already-exists" | undefined {
  const records = r.state.records;
  const saved: Records = {
    keyed: new Map([...records.keyed].map(([k, v]) => [k, new Map(v)])),
    singles: new Map(records.singles),
  };
  const written: Written = { rows: new Map(), duplicated: new Map() };
  for (const e of events) apply(r, e, written);
  if ([...written.duplicated.values()].every((keys) => keys.size === 0) && !uniqueTaken(r, written.rows))
    return undefined;
  records.keyed.clear();
  for (const [k, v] of saved.keyed) records.keyed.set(k, v);
  records.singles.clear();
  for (const [k, v] of saved.singles) records.singles.set(k, v);
  return "already-exists";
}

export function integrityViolations(r: Run, command: DefinitionRef): (Fault & Located)[] {
  const records = r.state.records;
  const found: (Fault & Located)[] = [];
  for (const name of r.st.entities) {
    const entity = ref(r.st, name);
    const rows: readonly [string | undefined, Fields][] = r.st.singles.includes(name)
      ? [[undefined, (records.singles.get(name) as Row).value]]
      : [...(records.keyed.get(name) ?? [])].map(([key, row]) => [key, row.value]);
    for (const [key, row] of rows) {
      const failing = r.functions.invariant(name, row);
      if (failing instanceof Failed) found.push(issueViolation(entity, failing));
      else if (failing)
        found.push(
          key === undefined
            ? { kind: "Fault.failedSingleInvariant", definition: entity, data: { condition: failing, command } }
            : {
                kind: "Fault.failedEntityInvariant",
                definition: entity,
                data: { recordKey: key, condition: failing, command },
              },
        );
      for (const { entity: owner, field, target } of r.st.references) {
        if (owner !== name || row[field] === null || row[field] === undefined) continue;
        const targetRows = records.keyed.get(target);
        if (targetRows === undefined || targetRows.has(String(row[field]))) continue;
        const dangling = { field, targetKey: String(row[field]), command };
        found.push(
          key === undefined
            ? { kind: "Fault.danglingSingleRef", definition: entity, data: dangling }
            : { kind: "Fault.danglingRef", definition: entity, data: { recordKey: key, ...dangling } },
        );
      }
    }
  }
  const failing = r.functions.serviceInvariant(recordSource(r.state.records, r.note));
  // A service is not a definition, so a violation of its invariants is located at the service.
  const location = r.place;
  if (failing instanceof Failed) {
    const { issue, error } = failing;
    const schema = issue.kind === "thrown" ? issue.schema : undefined;
    const definition = schema === undefined ? null : schemaOwner(schema);
    found.push(withExtra({ kind: "Fault.exception", definition, data: {} }, { error, location }));
  } else if (failing)
    found.push(
      withExtra(
        { kind: "Fault.failedServiceInvariant", definition: null, data: { condition: failing, command } },
        { location },
      ),
    );
  return found;
}
