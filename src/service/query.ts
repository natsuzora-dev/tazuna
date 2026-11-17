import type { Answer } from "../data/trace.generated.ts";
import { type Obligation, rejectedBy } from "../data/uncovered.ts";
import { withExtra } from "../data/violation.ts";
import { ref, requirementsOf, type Service } from "./basic.ts";
import { firstFalse } from "./contract.ts";
import { type Checked, Failed, type Functions, issueViolation } from "./functions.ts";
import { recordSource } from "./records.ts";
import { failedEnsures, halt, type Run, report, reportAll, write } from "./state.ts";

export function normalizeOutput(st: Service, functions: Functions, name: string, output: unknown): Checked | Failed {
  return functions.normalize({ kind: "output", definition: ref(st, name) }, output);
}

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
    (condition) => r.functions.inputRequirement(name, condition, input),
    requirementsOf(r.st, name).requires,
  );
  if (reason instanceof Failed) return halt(issueViolation(definition, reason));
  if (reason !== undefined)
    return done(
      { result: "rejected", rejection: { kind: "requires", reason } },
      rejectedBy(definition, { condition: reason }),
    );
  const records = recordSource(r.state.records, r.note);
  const resolved = r.functions.resolve(name, input, records, r.state.now);
  if (resolved instanceof Failed) return halt(issueViolation(definition, resolved));
  const output = normalizeOutput(r.st, r.functions, name, resolved);
  if (output instanceof Failed) return halt(issueViolation(definition, output));
  if ("error" in output)
    return report(r.state, withExtra({ kind: "Fault.outputSchema", definition, data: {} }, { error: output.error }));
  const failed = r.functions.queryEnsures(name, input, output.value, records);
  if (failed instanceof Failed) return halt(issueViolation(definition, failed));
  if (failed !== undefined) reportAll(r.state, [failedEnsures(definition, failed)]);
  return done({ result: "fulfilled", output: output.encoded }, { kind: "successAnswer", definition, data: {} });
}

/** Writes the changed answers of the open subscriptions. */
export function publish(r: Run): void {
  const { subscriptions } = r.state;
  for (const [id, s] of subscriptions.entries()) {
    const answer = resolveChecked(r, s.query, s.input);
    const compared = r.functions.comparable(s.query, answer);
    if (compared instanceof Failed) halt(issueViolation(ref(r.st, s.query), compared));
    if (subscriptions.repeats(id, compared)) continue;
    write(r.state, { dir: "out", type: "answer", to: id, answer });
  }
}
