import type { Answer } from "../data/trace.generated.ts";
import { type Obligation, rejectedBy } from "../data/uncovered.ts";
import { byCodePoint, canonicalJson, type Fields, type Json } from "../data/values.ts";
import { withExtra } from "../data/violation.ts";
import { emitsOf, named, traceNameOfRef } from "../spec/structure.ts";
import { ref, refOf, type Service } from "./basic.ts";
import { commandEnsures, requirementsRejection } from "./contract.ts";
import { Failed, issueViolation } from "./functions.ts";
import { applyAll, type Encoded, integrityViolations, writtenRecord } from "./integrity.ts";
import type { Emit, Emitted } from "./message.ts";
import { recordSource } from "./records.ts";
import { halt, type Run, report, reportAll, write } from "./state.ts";

/** Returns whether the command `command` lists the event of `e` in its emits. */
function lists(st: Service, command: string, e: Emit): boolean {
  return emitsOf(st.structure, ref(st, command)).some((l) => l !== null && traceNameOfRef(l, st.service) === e.event);
}

/** Lean's orderedGroups: the groups of `decided` with the events of `events`, each group in canonical JSON order. */
function orderedGroups(decided: readonly (readonly unknown[])[], events: readonly Encoded[]): Encoded[][] {
  const text = (e: Encoded) => canonicalJson({ event: e.emit.event, payload: e.encoded });
  let start = 0;
  return decided.map((g) => {
    start += g.length;
    return events.slice(start - g.length, start).toSorted((a, b) => byCodePoint(text(a), text(b)));
  });
}

/** Lean's twiceWritten: a record that two events of one group write. */
function twiceWritten(st: Service, groups: readonly (readonly Encoded[])[]) {
  for (const group of groups) {
    const rows = group.flatMap((e) => writtenRecord(st, e) ?? []);
    const twice = rows.find(
      (row, i) => rows.findIndex((other) => other.entity === row.entity && other.key === row.key) < i,
    );
    if (twice !== undefined) return twice;
  }
  return undefined;
}

export function processCommand(
  r: Run,
  name: string,
  encoded: unknown,
  id: string | undefined,
  step: number,
): { readonly answer: Answer; readonly groups: readonly (readonly Emitted[])[] } {
  const s = r.state;
  const definition = ref(r.st, name);
  r.note.reached({ kind: "request", definition, data: {} });
  const done = (answer: Answer, reached?: Obligation, groups: readonly (readonly Encoded[])[] = []) => {
    if (id !== undefined) write(s, { dir: "out", type: "answer", to: id, answer });
    const events = groups.flat();
    const lengths = groups.map((g) => g.length);
    if (events.length > 0) r.note.events(step, s.lines.length, lengths);
    for (const e of events)
      write(s, {
        dir: "out",
        type: "event",
        name: e.emit.event,
        payload: e.encoded,
        ...(id === undefined ? {} : { resultOf: id }),
      });
    if (reached !== undefined) r.note.reached(reached);
    return { answer, groups: groups.map((g) => g.map((e) => e.emit)) };
  };
  const parsed = r.functions.parse({ kind: "input", definition }, encoded);
  if (parsed instanceof Failed) return halt(issueViolation(definition, parsed));
  if ("error" in parsed) return done({ result: "rejected", rejection: { kind: "invalid-input" } });
  const input = parsed.value;
  const records = recordSource(s.records, r.note);
  const rejected = requirementsRejection(r, name, input, records);
  if (rejected !== undefined)
    return done(
      { result: "rejected", rejection: rejected.rejection },
      rejected.unmet && rejectedBy(definition, rejected.unmet),
    );
  const decided = r.functions.decide(name, input, records, s.now);
  if (decided instanceof Failed) return halt(issueViolation(definition, decided));
  const unlisted = decided.flat().find((e) => !lists(r.st, name, e));
  if (unlisted !== undefined) {
    const event = named(r.st.structure, r.st.service, unlisted.event, ["event"]);
    return report(s, {
      kind: "Fault.unlistedEmittedEvent",
      definition,
      data: { event: event === undefined ? null : { service: event.service, name: event.name } },
    });
  }
  const normalized = decided.flat().map((e): Encoded => {
    const event = refOf(r.st, e.event);
    const payload = r.functions.normalize({ kind: "payload", event }, e.payload);
    if (payload instanceof Failed) return halt(issueViolation(definition, payload));
    if ("error" in payload)
      return report(
        s,
        withExtra({ kind: "Fault.emittedPayloadSchema", definition, data: { event } }, { error: payload.error }),
      );
    const encoded = payload.encoded as Fields;
    return { emit: { event: e.event, payload: payload.value, encoded: encoded as Json }, encoded };
  });
  const groups = orderedGroups(decided, normalized);
  const twice = twiceWritten(r.st, groups);
  if (twice !== undefined)
    return report(s, {
      kind: "Fault.sameRecordInBag",
      definition,
      data: { entity: ref(r.st, twice.entity), recordKey: twice.key ?? null },
    });
  if (applyAll(r, groups.flat()) === "already-exists")
    return done({ result: "rejected", rejection: { kind: "already-exists" } });
  const violations = r.evaluations.quietly(() => [
    ...commandEnsures(r, name, input, records, recordSource(s.records, r.note)),
    ...integrityViolations(r, definition),
  ]);
  reportAll(s, violations);
  return done({ result: "accepted" }, { kind: "successAnswer", definition, data: {} }, groups);
}
