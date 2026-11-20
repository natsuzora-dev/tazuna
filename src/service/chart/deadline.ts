import { expectFound } from "../../data/internalError.ts";
import type { Delay } from "../../spec/structure.generated.ts";
import { delayMs, type StateStructure } from "../../spec/structure.ts";
import { ref } from "../basic.ts";
import { Failed, issueViolation } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { type Deadline, halt, type Instance, NoteAccess, type State, scopeOf } from "../state.ts";
import type { Processing } from "./queue.ts";

/** Lean's Time.inRange: whether the run's time can hold `ms`, an instant from year 0000 through year 9999. */
const inRange = (ms: bigint): boolean => -62_167_219_200_000n <= ms && ms < 253_402_300_800_000n;

/**
 * Lean's instantTime?: the instant that `text` writes, when the run's time can hold it and renderTime writes it back
 * as `text`. parseTime reads a four-digit year, and renderTime writes whole milliseconds.
 */
function instantTime(text: string): Temporal.Instant | undefined {
  if (!/^\d{4}-/.test(text)) return undefined;
  const instant = Temporal.Instant.from(text);
  return instant.epochNanoseconds % 1_000_000n === 0n &&
    inRange(instant.epochNanoseconds / 1_000_000n) &&
    instant.toString() === text
    ? instant
    : undefined;
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
    const data = { state, deadline: name };
    if (deadline.kind === "delay") {
      const ms =
        r.state.now.epochNanoseconds / 1_000_000n +
        expectFound(`delay in milliseconds of ${name}`, delayMsOf(deadline.delay));
      if (!inRange(ms)) halt({ kind: "Fault.deadlineOutOfRange", definition, data });
      r.state.deadlines.push({
        time: Temporal.Instant.fromEpochMilliseconds(Number(ms)),
        machine: instance.id,
        state,
        name,
        armedBy: step,
      });
      continue;
    }
    const time = computedTime(r, instance, state, name);
    if (time === undefined) halt({ kind: "Fault.atSchema", definition, data });
    r.state.deadlines.push({ time, machine: instance.id, state, name, armedBy: step });
  }
}

const delayMsOf = (delay: Delay | null): bigint | undefined => (delay === null ? undefined : delayMs(delay));

/** Returns the instant that the deadline's `at` computes, or undefined when it computes none. */
function computedTime(r: Processing, instance: Instance, state: string, name: string): Temporal.Instant | undefined {
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const computed = r.functions.deadlineAt(scope, records, name, new NoteAccess(r, scope));
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
