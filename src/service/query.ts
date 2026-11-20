import { expectFound } from "../data/internalError.ts";
import type { Answer } from "../data/trace.generated.ts";
import { type Obligation, rejectedBy } from "../data/uncovered.ts";
import { ref } from "./basic.ts";
import { Failed, firstFalse, issueViolation, sorted } from "./functions.ts";
import { recordSource } from "./records.ts";
import { failedEnsures, halt, type Run, reportAll, write } from "./state.ts";

export function resolveChecked(r: Run, name: string, encoded: unknown): Answer {
  const definition = ref(r.st, name);
  r.note.reached({ kind: "request", definition, data: {} });
  const done = (answer: Answer, reached: Obligation) => {
    r.note.reached(reached);
    return answer;
  };
  const parsed = r.functions.parse({ kind: "input", definition }, encoded ?? {});
  if (parsed instanceof Failed) return halt(issueViolation(definition, parsed));
  if ("error" in parsed) return { result: "rejected", rejection: { kind: "invalid-input" } };
  const input = parsed.value;
  const reason = firstFalse(
    (condition) => r.functions.inputRequirement(definition, condition, input),
    expectFound(`requirements of ${name}`, r.st.requirements.get(name)).requires,
  );
  if (reason instanceof Failed) return halt(issueViolation(definition, reason));
  if (reason !== undefined)
    return done(
      { result: "rejected", rejection: { kind: "requires", reason } },
      rejectedBy(definition, { condition: reason }),
    );
  const records = recordSource(r.state.records, r.note);
  const resolved = r.functions.resolve(name, input, records, r.state.now);
  if (resolved instanceof Failed)
    return halt(issueViolation(definition, resolved, () => ({ kind: "Fault.outputSchema", definition, data: {} })));
  const schema = { kind: "output", definition } as const;
  const output = sorted(r.st, schema, resolved);
  const failed = r.functions.queryEnsures(name, input, r.functions.decode(schema, output), records);
  if (failed instanceof Failed) return halt(issueViolation(definition, failed));
  if (failed !== undefined) reportAll(r.state, [failedEnsures(definition, failed)]);
  return done({ result: "fulfilled", output }, { kind: "successAnswer", definition, data: {} });
}

/** Writes the changed answers of the open subscriptions. */
export function publish(r: Run): void {
  const { subscriptions } = r.state;
  for (const [id, s] of subscriptions.entries()) {
    const answer = resolveChecked(r, s.query, s.input);
    const compared = r.functions.comparable(s.query, answer);
    if (compared instanceof Failed) halt(issueViolation(ref(r.st, s.query), compared));
    if (subscriptions.repeats(id, compared)) continue;
    write(r.state, { dir: "out", type: "answer", to: id, answer, request: ref(r.st, s.query) });
  }
}
