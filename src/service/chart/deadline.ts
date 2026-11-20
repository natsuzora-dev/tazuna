import { expectFound } from "../../data/internalError.ts";
import type { Delay } from "../../spec/structure.generated.ts";
import { delayMs, type StateStructure } from "../../spec/structure.ts";
import { ref } from "../basic.ts";
import { Failed, issueViolation } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { type Deadline, halt, type Instance, NoteAccess, type State, scopeOf } from "../state.ts";
import type { Processing } from "./queue.ts";

/**
 * Lean's instantTime?: the instant that `text` writes, when renderTime writes it back as `text`. parseTime reads a
 * four-digit year, and renderTime writes whole milliseconds.
 */
function instantTime(text: string): Temporal.Instant | undefined {
  if (!/^\d{4}-/.test(text)) return undefined;
  const instant = Temporal.Instant.from(text);
  return instant.epochNanoseconds % 1_000_000n === 0n && instant.toString() === text ? instant : undefined;
}

/** Lean's addDeadlines: arms the `after` deadlines of `state`, each time fixed now: now plus its delay, or its `at`. */
export function addDeadlines(
  r: Processing,
  instance: Instance,
  state: string,
  deadlines: StateStructure["deadlines"],
  step: number,
): void {
  for (const deadline of deadlines) {
    const { name } = deadline;
    const definition = ref(r.st, instance.chart.name);
    const time = deadline.kind === "delay" ? delayed(r, deadline.delay, name) : computedTime(r, instance, state, name);
    if (time === undefined) halt({ kind: "Fault.atSchema", definition, data: { state, deadline: name } });
    r.state.deadlines.push({ time, machine: instance.id, state, name, armedBy: step });
  }
}

/** Returns now plus `delay`, which check makes a length in milliseconds (Illegal.inexactDelay). */
function delayed(r: Processing, delay: Delay | null, name: string): Temporal.Instant {
  const ms = expectFound(`delay in milliseconds of ${name}`, delay === null ? undefined : delayMs(delay));
  return r.state.now.add({ milliseconds: ms });
}

/** Returns the instant that the deadline's `at` computes, or undefined when it computes none. */
function computedTime(r: Processing, instance: Instance, state: string, name: string): Temporal.Instant | undefined {
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const computed = r.functions.deadlineTime(scope, records, name, new NoteAccess(r, scope));
  if (computed instanceof Failed) halt(issueViolation(ref(r.st, instance.chart.name), computed));
  return computed === undefined ? undefined : instantTime(computed);
}

/** Removes `deadline` and returns whether it was still waiting. */
export function takeDeadline(s: State, deadline: Deadline): boolean {
  const index = s.deadlines.indexOf(deadline);
  if (index < 0) return false;
  s.deadlines.splice(index, 1);
  return true;
}
