import { finished } from "../../spec/tree.ts";
import { ref } from "../basic.ts";
import { Failed, issueViolation, sorted } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { failedEnsures, halt, type Instance, NoteAccess, reportAll, scopeOf, startQueued } from "../state.ts";
import { endWith, exitFuel } from "./exit.ts";
import type { Processing } from "./queue.ts";

export function enterFinal(r: Processing, instance: Instance, parent: string, step: number): void {
  const finishing = finished(instance.chart.tree, instance.entered, parent);
  const waiting = instance.awaitingOnDone;
  if (waiting !== undefined) {
    instance.awaitingOnDone = [...waiting, ...finishing];
    return;
  }
  instance.awaitingOnDone = finishing;
  r.queue.tasks.push({ kind: "onDone", machine: instance.id, cause: step });
}

/** Closes a screen that entered its root final state, and queues its opener's onDone work. */
export function closeFinal(r: Processing, instance: Instance, step: number): void {
  const definition = ref(r.st, instance.chart.name);
  const scope = scopeOf(r.state, instance, null);
  const closed = r.functions.close(scope, new LazyRecordSource(r.state.records, r.note), new NoteAccess(r, scope));
  if (closed instanceof Failed)
    halt(issueViolation(definition, closed, () => ({ kind: "Fault.screenOutputSchema", definition, data: {} })));
  const schema = { kind: "output", definition } as const;
  const encoded = sorted(r.st, schema, closed);
  const output = r.functions.decode(schema, encoded);
  const failed = r.functions.closeEnsures(instance.chart.name, instance.input, output);
  if (failed instanceof Failed) halt(issueViolation(definition, failed));
  if (failed !== undefined) reportAll(r.state, [failedEnsures(definition, failed)]);
  endWith(r, instance.id, exitFuel(r.st));
  const { id } = instance;
  if (id.kind !== "opened") return;
  r.queue.tasks.push({
    kind: "opensDone",
    machine: id.opener,
    state: id.state,
    key: id.key,
    output,
    serial: startQueued(r.state, id.opener, id.state),
    cause: step,
  });
}
