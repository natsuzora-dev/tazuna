import { newQueue, type Processing } from "../service/chart/queue.ts";
import type { Functions } from "../service/functions.ts";
import type { Note } from "../service/note.ts";
import type { Evaluations, Instance } from "../service/state.ts";

/**
 * Returns a copy of `instance`. Spec values, context, input, awaitingOnDone and the arrays in lastChildren and copyKeys
 * are replaced rather than changed, so the copy shares them.
 */
function copyInstance(instance: Instance): Instance {
  return {
    ...instance,
    entered: new Map(instance.entered),
    lastChildren: new Map(instance.lastChildren),
    shown: new Map(instance.shown),
    copyKeys: new Map(instance.copyKeys),
  };
}

/**
 * Returns the processing to continue with other inputs, asking `functions` and with `listener` listening. Clone only
 * after an input that completed without halting: then the queue is empty, no transition is assigning or exiting, and
 * every entered state's activities have been sent, so only what carries over to the next input is copied. Spec
 * definitions, schemas, Temporal values, spec functions, and the entries of the trace, violations, steps and mocks,
 * which are never changed once written, are shared. A mock's request is read only for its id and activity.
 */
export function clone(r: Processing, functions: Functions, listener: Note & Evaluations): Processing {
  const s = r.state;
  return {
    state: {
      now: s.now,
      started: s.started,
      records: {
        keyed: new Map([...s.records.keyed].map(([name, rows]) => [name, new Map(rows)])),
        singles: new Map(s.records.singles),
      },
      commandAnswers: new Map(s.commandAnswers),
      eventDeliveries: new Map(s.eventDeliveries),
      machines: new Map([...s.machines].map(([resource, instance]) => [resource, copyInstance(instance)])),
      copies: new Map([...s.copies].map(([resource, copy]) => [resource, copyInstance(copy)])),
      stack: [...s.stack],
      deadlines: s.deadlines.map((t) => ({ ...t })),
      inputDeadlineOrder: s.inputDeadlineOrder,
      deadlineOrder: s.deadlineOrder,
      stepOrder: s.stepOrder,
      pending: s.pending.map((p) => ({ ...p })),
      queued: s.queued.map((q) => ({ ...q })),
      serial: s.serial,
      turn: s.turn,
      lines: [...s.lines],
      lineCounts: new Map(s.lineCounts),
      steps: [...s.steps],
      messageCount: s.messageCount,
      created: [...s.created],
      keyNames: new Map(s.keyNames),
      keyCalls: [...s.keyCalls],
      subscriptions: s.subscriptions.clone((subscription) => subscription),
      results: new Map([...s.results].map(([id, a]) => [id, { ...a, events: [...a.events] }])),
      mocks: new Map(s.mocks),
      subscribed: new Map(s.subscribed),
      violations: [...s.violations],
    },
    queue: newQueue(),
    st: r.st,
    functions,
    note: listener,
    evaluations: listener,
    place: r.place,
  };
}
