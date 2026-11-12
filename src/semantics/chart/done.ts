import { finished } from "../../syntax/tree.ts";
import { Failed, issueViolation } from "../functions.ts";
import { limits } from "../limits.ts";
import { ref } from "../service/basic.ts";
import { LazyRecordSource } from "../service/records.ts";
import { failedEnsures, halt, type Instance, NoteAccess, reportAll, scopeOf, startQueued } from "../state.ts";
import { endWith } from "./exit.ts";
import type { Processing } from "./queue.ts";

export function enterFinal(r: Processing, instance: Instance, parent: string, step: number): void {
  const finishing = finished(instance.chart.tree, instance.entered, parent);
  const waiting = instance.awaitingOnDone;
  if (waiting !== undefined) {
    instance.awaitingOnDone = [...waiting, ...finishing];
    return;
  }
  instance.awaitingOnDone = finishing;
  r.queue.tasks.push({ kind: "onDone", machine: instance.resource, cause: step });
}

/** Closes a screen that entered its root final state, and queues its opener's onDone work. */
export function closeFinal(r: Processing, instance: Instance, step: number): void {
  const definition = ref(r.st, instance.chart.name);
  const scope = scopeOf(r.state, instance, null);
  const closed = r.functions.close(scope, new LazyRecordSource(r.state.records, r.note), new NoteAccess(r, scope));
  if (closed instanceof Failed)
    halt(issueViolation(definition, closed, () => ({ kind: "Fault.screenOutputSchema", definition, data: {} })));
  const { output, failed } = closed;
  if (failed !== undefined) reportAll(r.state, [failedEnsures(definition, failed)]);
  endWith(r, instance.resource, limits.exitDepth);
  const opener = instance.opener;
  if (opener === undefined) return;
  r.queue.tasks.push({
    kind: "opensDone",
    machine: opener.parent,
    state: opener.state,
    key: opener.key,
    output,
    serial: startQueued(r.state, opener.parent, opener.state),
    cause: step,
  });
}
