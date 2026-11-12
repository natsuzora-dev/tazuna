import type { Answer } from "../../data/trace.generated.ts";
import { type Obligation, rejectedBy } from "../../data/uncovered.ts";
import type { Fields } from "../../data/values.ts";
import { withExtra } from "../../data/violation.ts";
import { emitsOf, named, traceNameOfRef } from "../../syntax/structure.ts";
import { Failed, issueViolation } from "../functions.ts";
import type { Emit } from "../message.ts";
import { halt, type Run, report, reportAll, write } from "../state.ts";
import { ref, refOf, type Service } from "./basic.ts";
import { commandEnsures, requirementsRejection } from "./contract.ts";
import { applyAll, type Encoded, integrityViolations } from "./integrity.ts";
import { recordSource } from "./records.ts";

/** Returns whether the command `command` lists the event of `e` in its emits. */
function lists(st: Service, command: string, e: Emit): boolean {
  return emitsOf(st.structure, ref(st, command)).some((l) => l !== null && traceNameOfRef(l, st.service) === e.event);
}

export function processCommand(
  r: Run,
  name: string,
  encoded: unknown,
  id: string | undefined,
  step: number,
): { readonly answer: Answer; readonly emits: readonly Emit[] } {
  const s = r.state;
  const definition = ref(r.st, name);
  r.note.reached({ kind: "request", definition, data: {} });
  const done = (answer: Answer, reached?: Obligation, events: readonly Encoded[] = []) => {
    if (id !== undefined) write(s, { dir: "out", type: "answer", to: id, answer });
    if (events.length > 0) r.note.events(step, s.lines.length, events.length);
    for (const e of events) write(s, { dir: "out", type: "event", name: e.emit.event, payload: e.encoded });
    if (reached !== undefined) r.note.reached(reached);
    return { answer, emits: events.map((e) => e.emit) };
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
  const unlisted = decided.find((e) => !lists(r.st, name, e));
  if (unlisted !== undefined) {
    const event = named(r.st.structure, r.st.service, unlisted.event, ["event"]);
    return report(s, {
      kind: "Fault.unlistedEmittedEvent",
      definition,
      data: { event: event === undefined ? null : { service: event.service, name: event.name } },
    });
  }
  const events = decided.map((e): Encoded => {
    const event = refOf(r.st, e.event);
    const payload = r.functions.normalize({ kind: "payload", event }, e.payload);
    if (payload instanceof Failed) return halt(issueViolation(definition, payload));
    if ("error" in payload)
      return report(
        s,
        withExtra({ kind: "Fault.emittedPayloadSchema", definition, data: { event } }, { error: payload.error }),
      );
    return { emit: { event: e.event, payload: payload.value }, encoded: payload.encoded as Fields };
  });
  if (applyAll(r, events) === "already-exists")
    return done({ result: "rejected", rejection: { kind: "already-exists" } });
  const violations = r.evaluations.quietly(() => [
    ...commandEnsures(r, name, input, records, recordSource(s.records, r.note)),
    ...integrityViolations(r, definition),
  ]);
  reportAll(s, violations);
  return done({ result: "accepted" }, { kind: "successAnswer", definition, data: {} }, events);
}
