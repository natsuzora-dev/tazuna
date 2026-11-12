import { comparable, comparableAnswer } from "../data/canonical.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { type FileLine, parseFileLines, untilMalformed } from "../data/trace.ts";
import type { Shape } from "../data/values.ts";
import type { Spec } from "../load/load.ts";
import { definitionOfTraceName, refOfDefinition } from "../load/traceName.ts";
import { contractsListing } from "../syntax/structure.ts";
import { type Compared, compare } from "./compare.ts";
import { byLine } from "./lines.ts";

function canonicalLine(spec: Spec, service: string): (l: TraceLine) => TraceLine {
  const outputByRequestId = new Map<string, Shape>();
  return (l) => {
    switch (l.type) {
      case "operation":
      case "unacceptedOperation": {
        const [screen, control = ""] = l.name.split(".");
        const def = definitionOfTraceName(spec, service, screen, "screen");
        return { ...l, payload: comparable(def?.controls?.[control]?.payload, l.payload) };
      }
      case "answer":
        return { ...l, answer: comparableAnswer(l.answer, outputByRequestId.get(l.to)) };
      case "event": {
        const def = definitionOfTraceName(spec, service, l.name, "event");
        return def === undefined ? l : { ...l, payload: comparable(def.payload, l.payload) };
      }
      case "command":
      case "query":
      case "subscribe": {
        const def = definitionOfTraceName(spec, service, l.name, l.type === "command" ? "command" : "query");
        if (def === undefined) return l;
        if (def.output !== undefined && l.id !== undefined) outputByRequestId.set(l.id, def.output);
        return { ...l, input: comparable(def.input, l.input) };
      }
      case "unsubscribe":
      case "time":
      case "restart":
        return l;
    }
  };
}

function withoutRepeatedAnswers(lines: readonly (TraceLine | undefined)[]): (TraceLine | undefined)[] {
  const open = new Subscriptions<undefined>();
  return lines.map((l) => {
    if (l?.dir === "in" && l.type === "subscribe" && l.id !== undefined) open.subscribe(l.id, undefined);
    else if (l?.dir === "in" && l.type === "unsubscribe") open.unsubscribe(l.to);
    else if (l?.dir === "out" && l.type === "answer" && open.repeats(l.to, l.answer)) return undefined;
    return l;
  });
}

function internalEvent(spec: Spec, service: string): (l: TraceLine) => boolean {
  return (l) => {
    if (l.dir !== "out" || l.type !== "event") return false;
    const def = definitionOfTraceName(spec, service, l.name, "event");
    return def !== undefined && contractsListing(spec.structure, refOfDefinition(spec, def)).length === 0;
  };
}

/** Compares the trace with the snapshot's lines. A trace line's violation has its 1-based line number in data.line. */
export function compareTrace(
  spec: Spec,
  service: string,
  snapshot: readonly (TraceLine | undefined)[],
  trace: readonly unknown[],
): Compared {
  const { found, bindings } = verifyLines(spec, service, snapshot, parseFileLines(trace));
  return { found: found.sort(byLine), bindings };
}

export function verifyLines(
  spec: Spec,
  service: string,
  snapshot: readonly (TraceLine | undefined)[],
  trace: readonly FileLine[],
): Compared {
  const { lines, malformed } = untilMalformed(trace);
  const ofService = canonicalLine(spec, service);
  return compare(
    snapshot.map((l) => l && ofService(l)),
    withoutRepeatedAnswers(lines.map((l) => l && ofService(l))),
    malformed,
    internalEvent(spec, service),
  );
}
