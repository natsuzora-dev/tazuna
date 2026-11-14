import { byCodePoint, type Fields } from "../../data/values.ts";
import type { Note } from "../note.ts";

/** A keyed entity's row: decoded for spec functions, and encoded as Lean holds it, which uniqueness compares. */
export interface Row {
  readonly value: Fields;
  readonly encoded: Fields;
}

/** Lean's Records as a store: the rows of each keyed entity by key, and the row of each single entity. */
export interface Records {
  readonly keyed: Map<string, Map<string, Row>>;
  readonly singles: Map<string, Row>;
}

/** The only access to records, where each call is a read. A single entity's fields take no key. */
export interface RecordSource {
  keys(entity: string): readonly string[];
  exists(entity: string, key: string): boolean;
  field(entity: string, key: string | undefined, field: string): unknown;
}

/**
 * Returns `records` as spec functions read them, telling `note` each read. The source is a copy taken at the call, so
 * it keeps the records from before a later write: ensures reads `before` after applyAll.
 */
export function recordSource(records: Records, note: Note): RecordSource {
  const keyed = new Map([...records.keyed].map(([name, rows]) => [name, new Map(rows)]));
  const singles = new Map(records.singles);
  return {
    keys: (entity) => {
      note.readRecord({ entity });
      return [...(keyed.get(entity)?.keys() ?? [])].sort(byCodePoint);
    },
    exists: (entity, key) => {
      note.readRecord({ entity, key });
      return keyed.get(entity)?.has(key) ?? false;
    },
    field: (entity, key, field) => {
      note.readRecord(key === undefined ? { entity, field } : { entity, key, field });
      return (key === undefined ? singles.get(entity) : keyed.get(entity)?.get(key))?.value[field];
    },
  };
}

/** A recordSource taken at the first read, so that a Scope question whose expressions read no record copies nothing. */
export class LazyRecordSource implements RecordSource {
  private readonly records: Records;
  private readonly note: Note;
  private source: RecordSource | undefined;

  constructor(records: Records, note: Note) {
    this.records = records;
    this.note = note;
  }

  private taken(): RecordSource {
    this.source ??= recordSource(this.records, this.note);
    return this.source;
  }

  keys(entity: string): readonly string[] {
    return this.taken().keys(entity);
  }

  exists(entity: string, key: string): boolean {
    return this.taken().exists(entity, key);
  }

  field(entity: string, key: string | undefined, field: string): unknown {
    return this.taken().field(entity, key, field);
  }
}
