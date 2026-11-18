import type { ChoiceDependent } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { deliveryOrderLimit } from "../data/limits.generated.ts";
import type { Scenario } from "../data/scenario.generated.ts";
import { type Violation, withExtra } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { sameLineId } from "../service/message.ts";
import type { Message, World } from "../sim/network.ts";
import { receivedId } from "../sim/receive.ts";
import { targetOf } from "../sim/resolve.ts";
import { executeSpec, type Made } from "../sim/spec/simulate.ts";
import { deliveryOrder, type Outcome } from "./choiceDependent.ts";
import { compareOf, outcomeFor } from "./stepOrders.ts";

/** Lean's injections. */
function injections(n: number, h: number): number[][] {
  if (h === 0) return [[]];
  return injections(n, h - 1).flatMap((p) =>
    Array.from({ length: n }, (_, x) => x)
      .filter((x) => !p.includes(x))
      .map((x) => [...p, x]),
  );
}

/** Lean's definitionOf?. */
function definitionOf(w: World, m: Message): DefinitionRef | undefined {
  const requested = (to: Message["id"]) => {
    for (const r of w.messages) if (sameLineId(receivedId(r.sender, r.id), to)) return targetOf(r);
    return undefined;
  };
  const b = m.body;
  if (b.type === "command" || b.type === "query" || b.type === "subscribe") return b.target;
  if (b.type === "event") return b.event;
  if (b.type === "answer") return requested(b.to);
  if (b.type === "unsubscribe") return requested(receivedId(m.sender, b.to));
  return undefined;
}

/** Lean's Delivering. */
interface Delivering {
  readonly line: number;
  readonly count: number;
  readonly definition: DefinitionRef;
}

/** Lean's Execution.delivering. */
function delivering({ world: w }: Made): Delivering[] {
  const lines = [
    ...new Set(w.spans.flatMap((sp) => (sp.origin.type === "line" && sp.delivery > 0 ? [sp.origin.index] : []))),
  ];
  return lines.flatMap((line) => {
    const carried = w.carried.flatMap(([l, k]) => {
      const m = l === line ? w.messages[k] : undefined;
      return m === undefined ? [] : [m];
    });
    for (const m of carried) {
      const definition = definitionOf(w, m);
      if (definition !== undefined) return [{ line, count: carried.length, definition }];
    }
    return [];
  });
}

/** Lean's putBack: the lines of `service`, each delivery of line `line` it processed back at its message's place. */
function putBack<T>(w: World, service: string, line: number, order: readonly number[], lines: readonly T[]): T[] {
  const spans = w.spans.filter((sp) => sp.service === service && sp.origin.type === "line" && sp.origin.index === line);
  const [first, last] = [spans[0], spans.at(-1)];
  if (first === undefined || last === undefined || spans.some((sp, k) => k > 0 && spans[k - 1]?.to !== sp.from))
    return [...lines];
  const placed = spans
    .map((sp) => [order[sp.delivery] ?? sp.delivery, sp] as const)
    .toSorted(([a], [b]) => a - b)
    .flatMap(([, sp]) => lines.slice(sp.from, sp.to));
  return [...lines.slice(0, first.from), ...placed, ...lines.slice(last.to)];
}

/** Lean's Execution.putBackOutcome. */
function putBackOutcome(m: Made, service: string, line: number, order: readonly number[]): Outcome {
  const o = outcomeFor(m, service);
  return { ...o, lines: putBack(m.world, service, line, order, o.lines) };
}

/** Lean's DeliveryOrderTried. */
interface DeliveryOrderTried {
  readonly scenarioLine: number;
  readonly order: readonly number[];
  readonly found: ChoiceDependent | null;
}

/** Lean's DeliveryOrderSearch. The diff test asks Lean. */
export interface DeliveryOrderSearch {
  readonly tried: readonly DeliveryOrderTried[];
  readonly found: readonly ChoiceDependent[];
}

/** Lean's deliveryOrderSearch of the scenario `sc`, from its execution in sending order. */
export function deliveryOrderSearch(spec: Spec, sc: Scenario): DeliveryOrderSearch {
  const base = executeSpec(spec, sc);
  const tried: DeliveryOrderTried[] = [];
  const found: ChoiceDependent[] = [];
  for (const d of delivering(base)) {
    let count = 0;
    for (const order of injections(d.count, d.count).slice(1)) {
      if (count === deliveryOrderLimit) {
        found.push({
          kind: "ChoiceDependent.searchLimit",
          definition: d.definition,
          data: { limit: deliveryOrderLimit },
        });
        break;
      }
      count += 1;
      const alternative = executeSpec(spec, sc, [], new Map([[d.line, order]]));
      const outcomes = [...base.world.services.keys()].map(
        (service) => [service, outcomeFor(base, service), putBackOutcome(alternative, service, d.line, order)] as const,
      );
      const result = deliveryOrder((service) => compareOf(spec, service), d.definition, d.line, order, outcomes);
      tried.push({ scenarioLine: d.line, order, found: result ?? null });
      if (result !== undefined) {
        found.push(result);
        break;
      }
    }
  }
  return { tried, found };
}

/**
 * The violations of deliveryOrderSearch of the scenario `sc`, at the definitions they name, when its execution
 * `executed` has a line that delivered several messages to a running receiver.
 */
export function deliveryOrderChanges(spec: Spec, sc: Scenario, executed: Made): Violation[] {
  if (delivering(executed).length === 0) return [];
  return deliveryOrderSearch(spec, sc).found.map((v) => withExtra(v, { location: placeOf(spec, v.definition) }));
}
