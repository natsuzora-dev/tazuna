import { sameRef } from "../data/definitionRef.ts";
import type { Answer, LineId } from "../data/trace.generated.ts";
import { type Obligation, rejectedBy } from "../data/uncovered.ts";
import { byCodePoint, canonicalJson, type Fields } from "../data/values.ts";
import { ref, type Service } from "./basic.ts";
import { commandEnsures, requirementsRejection } from "./contract.ts";
import { Failed, issueViolation, lists, parseOutside } from "./functions.ts";
import { applyAll, type Encoded, integrityViolations, writtenRecord } from "./integrity.ts";
import type { Emitted } from "./message.ts";
import { recordSource } from "./records.ts";
import { halt, type Run, report, reportAll, write } from "./state.ts";

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
  id: LineId | undefined,
  step: number,
): { readonly answer: Answer; readonly groups: readonly (readonly Emitted[])[] } {
  const s = r.state;
  const definition = ref(r.st, name);
  r.note.reached({ kind: "request", definition, data: {} });
  const done = (answer: Answer, reached?: Obligation, groups: readonly (readonly Encoded[])[] = []) => {
    if (id !== undefined) write(s, { dir: "out", type: "answer", to: id, answer, request: definition });
    groups.forEach((g, group) => {
      for (const e of g)
        write(s, {
          dir: "out",
          type: "event",
          event: e.emit.event,
          payload: e.encoded,
          ...(id === undefined ? {} : { resultOf: id }),
          emitted: { step, group },
        });
    });
    if (reached !== undefined) r.note.reached(reached);
    return { answer, groups: groups.map((g) => g.map((e) => e.emit)) };
  };
  const parsed = parseOutside(r.st, r.functions, { kind: "input", definition }, encoded);
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
  if (decided instanceof Failed)
    return halt(
      issueViolation(definition, decided, (schema) =>
        schema.kind === "payload"
          ? { kind: "Fault.emittedPayloadSchema", definition, data: { event: schema.event } }
          : { kind: "Fault.exception", definition, data: {} },
      ),
    );
  const unlisted = decided.flat().find((e) => !lists(r.st, name, e));
  if (unlisted !== undefined) {
    const event = r.st.structure.definitions.find((d) => d.kind === "event" && sameRef(d, unlisted.event));
    return report(s, {
      kind: "Fault.unlistedEmittedEvent",
      definition,
      data: { event: event === undefined ? null : { service: event.service, name: event.name } },
    });
  }
  const emits = decided.flat().map(({ event, payload }): Encoded => {
    const decoded = r.functions.decode({ kind: "payload", event }, payload);
    return { emit: { event, payload: decoded, encoded: payload }, encoded: payload as Fields };
  });
  const groups = orderedGroups(decided, emits);
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
