import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Report } from "../data/report.generated.ts";
import type { GivenRecord, PeerEntry, Scenario } from "../data/scenario.generated.ts";
import { canonicalJson, type Fields } from "../data/values.ts";
import { ref, type Service, uniqueOf } from "../service/basic.ts";
import type { Processing } from "../service/chart/queue.ts";
import { Failed } from "../service/functions.ts";
import { type Row, recordSource } from "../service/records.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import { noteTo, type Participant, type Role, type World } from "./network.ts";

/** Lean's staticPeers. */
function staticPeers(structure: Structure, own: string): string[] {
  const named = (d: Structure["definitions"][number]): (DefinitionRef | null)[] => {
    switch (d.kind) {
      case "automation":
        return [d.receives, d.command];
      case "machine":
      case "screen":
        return [
          ...Object.values(d.receives),
          ...Object.values(d.commands),
          ...Object.values(d.queries),
          ...Object.values(d.screens),
        ];
      default:
        return [];
    }
  };
  const external = new Set(structure.services.filter((s) => s.external).map((s) => s.name));
  const found = new Set<string>();
  for (const d of structure.definitions)
    for (const r of named(d)) {
      if (r === null || r.service === d.service) continue;
      if (d.service === own) found.add(r.service);
      else if (r.service === own && !external.has(d.service)) found.add(d.service);
    }
  return [...found].sort();
}

/** Lean's peersOf. */
function peersOf(sc: Scenario): PeerEntry[] {
  const found: PeerEntry[] = [];
  for (const p of sc.given.peers)
    if (p.service !== sc.service && !found.some((q) => q.service === p.service)) found.push(p);
  return found;
}

/** Lean's World.start: `processingFor` makes each running service's processing. */
export function start(sc: Scenario, processingFor: (service: string) => Processing): World {
  const now = Temporal.Instant.from(sc.given.start);
  const peers = peersOf(sc);
  const roles = new Map<string, Role>([[sc.service, "own"], ...peers.map((p) => [p.service, p.role] as const)]);
  const running = [sc.service, ...peers.flatMap((p) => (p.role === "run" ? [p.service] : []))];
  const participants = new Map<string, Participant>(
    running.map((service) => {
      const processing = processingFor(service);
      processing.state.now = now;
      processing.state.keyOwner = service;
      return [service, { processing, halted: undefined }];
    }),
  );
  return {
    now,
    roles,
    participants,
    messages: [],
    spans: [],
    opened: [],
    sent: [],
    carried: [],
    inFlight: [],
    counts: new Map(),
    looked: [],
    reports: [],
    halted: undefined,
    stepOrders: [],
  };
}

/** Lean's givenRecords. */
function givenRecords(sc: Scenario, service: string): readonly GivenRecord[] {
  if (service === sc.service) return sc.given.records;
  const peer = peersOf(sc).find((p) => p.service === service);
  return peer?.role === "run" ? peer.records : [];
}

/** Lean's Row of a Given record, with the row that the TS records hold. */
interface GivenRow {
  readonly entity: string;
  readonly key: string | undefined;
  readonly row: Row;
}

/** Lean's clash. */
function clash(st: Service, a: GivenRow, b: GivenRow): boolean {
  if (a.entity !== b.entity) return false;
  if (a.key === b.key) return true;
  const unique = uniqueOf(st, a.entity);
  return (
    unique.length > 0 &&
    unique.every((f) => a.row.encoded[f] !== null) &&
    unique.every((f) => canonicalJson(a.row.encoded[f]) === canonicalJson(b.row.encoded[f]))
  );
}

/** Lean's givenRows. */
function givenRows(
  r: Processing,
  service: string,
  records: readonly GivenRecord[],
): { readonly rows: GivenRow[]; readonly reports: Report[] } {
  const rows: GivenRow[] = [];
  const reports: Report[] = [];
  for (const g of records) {
    const data = { service, entity: g.entity, key: g.key ?? null };
    const invalid = () => reports.push({ kind: "Report.invalidRecord", definition: null, data });
    if (!r.st.entities.includes(g.entity) || r.st.singles.includes(g.entity) !== (g.key === undefined)) {
      invalid();
      continue;
    }
    const checked = r.functions.parse({ kind: "record", entity: ref(r.st, g.entity) }, g.value);
    if (checked instanceof Failed || "error" in checked) {
      invalid();
      continue;
    }
    const row: GivenRow = {
      entity: g.entity,
      key: g.key,
      row: { value: checked.value, encoded: checked.encoded as Fields },
    };
    if (rows.some((earlier) => clash(r.st, earlier, row)))
      reports.push({ kind: "Report.duplicateRecord", definition: null, data });
    else rows.push(row);
  }
  return { rows, reports };
}

/** Lean's givenInvariants: `r` holds the rows as its records. */
function givenInvariants(r: Processing, service: string, rows: readonly GivenRow[]): Report[] {
  const broken = (entity: string | null, key: string | null, invariant: string | null): Report => ({
    kind: "Report.brokenGivenInvariant",
    definition: null,
    data: { service, entity, key, invariant },
  });
  return r.evaluations.quietly(() => {
    const found = rows.flatMap((row) => {
      const failing = r.functions.invariant(row.entity, row.row.value);
      if (failing instanceof Failed) return [broken(row.entity, row.key ?? null, null)];
      return failing === undefined ? [] : [broken(row.entity, row.key ?? null, failing)];
    });
    const whole = r.functions.serviceInvariant(recordSource(r.state.records, r.note));
    if (whole instanceof Failed) found.push(broken(null, null, null));
    else if (whole !== undefined) found.push(broken(null, null, whole));
    return found;
  });
}

/** Lean's World.given. */
export function given(w: World, structure: Structure, sc: Scenario): void {
  const peers = sc.given.peers;
  peers.forEach((p, k) => {
    if (p.service === sc.service || peers.slice(0, k).some((q) => q.service === p.service))
      noteTo(w, { kind: "Report.repeatedPeer", definition: null, data: { service: p.service } });
  });
  for (const service of staticPeers(structure, sc.service))
    if (!peers.some((p) => p.service === service))
      noteTo(w, { kind: "Report.unlistedPeer", definition: null, data: { service } });
  for (const [service, { processing: r }] of w.participants) {
    const written = givenRecords(sc, service);
    const { rows, reports } = givenRows(r, service, written);
    const { records } = r.state;
    for (const row of rows)
      if (row.key === undefined) records.singles.set(row.entity, row.row);
      else records.keyed.get(row.entity)?.set(row.key, row.row);
    const missing: Report[] = r.st.singles
      .filter((e) => !written.some((g) => g.entity === e))
      .map((entity) => ({
        kind: "Report.missingRecord",
        definition: null,
        data: { service, entity },
      }));
    const broken = reports.length === 0 && missing.length === 0 ? givenInvariants(r, service, rows) : [];
    for (const report of [...reports, ...missing, ...broken]) noteTo(w, report);
  }
}
