import type { DefinitionRef } from "../data/definitionRef.ts";
import type { LineId, TraceLine } from "../data/trace.generated.ts";
import { lineIdText, operationName } from "../data/trace.ts";
import { bodyContent, type Line } from "../service/message.ts";
import type { StepInfo } from "../service/state.ts";
import { traceNameOfRef } from "../spec/structure.ts";
import { ordered, windows } from "./order.ts";

/**
 * Lean's traceLineOf: the trace line of `line` of the trace of `service`, with its `after` and `created`. This is where
 * a definition gets its trace name and a line id its text.
 */
export function traceLineOf(
  service: string,
  line: Line,
  after: readonly LineId[] = [],
  created: readonly string[] = [],
): TraceLine {
  const extra = {
    ...(after.length > 0 ? { after: after.map(lineIdText) } : {}),
    ...(created.length > 0 ? { created: [...created] } : {}),
  };
  const { time, dir } = line;
  const id = lineIdText(line.id);
  const name = (r: DefinitionRef) => traceNameOfRef(r, service);
  switch (line.type) {
    case "command":
    case "query":
    case "subscribe":
      return { time, dir, type: line.type, id, name: name(line.target), input: line.input, ...extra };
    case "event":
      return {
        time,
        dir,
        type: "event",
        id,
        name: name(line.event),
        payload: line.payload,
        ...(line.resultOf === undefined ? {} : { resultOf: lineIdText(line.resultOf) }),
        ...extra,
      };
    case "answer":
      return { time, dir, type: "answer", id, to: lineIdText(line.to), answer: line.answer, ...extra };
    case "unsubscribe":
      return { time, dir, type: "unsubscribe", id, to: lineIdText(line.to), ...extra };
    case "time":
    case "restart":
      return { time, dir: "in", type: line.type, id, ...extra };
    case "operation":
      return {
        time,
        dir,
        type: "operation",
        id,
        name: operationName(name(line.screen), line.control),
        ...(line.nth === undefined ? {} : { nth: line.nth }),
        ...("payload" in line ? { payload: line.payload } : {}),
        ...extra,
      };
  }
}

/** The trace lines of `lines` of the trace of `service` as its snapshot holds them, with `after` and `created`. */
export function snapshotLines(
  service: string,
  lines: readonly Line[],
  steps: readonly StepInfo[],
  created: readonly string[],
): TraceLine[] {
  const after = new Map<number, number[]>();
  for (const window of windows(lines)) {
    for (const b of window) {
      const earlier = window.filter((a) => a < b && ordered(lines, steps, a, b));
      if (earlier.length > 0) after.set(b, earlier);
    }
  }
  const firstLine = new Map<string, number>();
  const visit = (value: unknown, i: number): void => {
    if (typeof value === "string") {
      if (created.includes(value) && !firstLine.has(value)) firstLine.set(value, i);
    } else if (value && typeof value === "object") for (const v of Object.values(value)) visit(v, i);
  };
  lines.forEach((l, i) => {
    if (l.dir === "out") visit(bodyContent(l), i);
  });
  return lines.map((l, i) =>
    traceLineOf(
      service,
      l,
      (after.get(i) ?? []).map((a) => (lines[a] as Line).id),
      created.filter((v) => firstLine.get(v) === i),
    ),
  );
}
