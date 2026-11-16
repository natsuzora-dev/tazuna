import type { Answer } from "../data/trace.generated.ts";
import { ref } from "./basic.ts";
import { byCallerKinds } from "./message.ts";
import { type Run, report } from "./state.ts";

export function automationAnswer(r: Run, a: string, answer: Answer): void {
  if (answer.result === "rejected" && byCallerKinds.has(answer.rejection.kind))
    report(r.state, {
      kind: "Fault.rejectedAutomationCommand",
      definition: ref(r.st, a),
      data: { rejection: answer.rejection },
    });
}
