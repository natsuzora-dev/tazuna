import { z } from "zod";
import type { Delay } from "../data/datetime.ts";
import type { Malformed } from "../data/malformed.ts";
import { stateAt } from "../dsl/chart.ts";
import type { ChartSpec, Contract, Definition, Named } from "../dsl/definition.ts";
import type { Scenario, StateInputs } from "../dsl/scenario.ts";
import type { ChartStructure } from "../syntax/structure.ts";
import type { Found } from "./found.ts";

const isoDatetime = z.iso.datetime({ offset: true });

/**
 * Returns whether the run can read `time` exactly. The run reads the time with Temporal, which rejects some times that
 * Zod accepts, such as ten fraction digits, and counts it in whole milliseconds, as Lean's time does.
 */
function readable(time: string): boolean {
  if (!isoDatetime.safeParse(time).success) return false;
  try {
    return Temporal.Instant.from(time).epochNanoseconds % 1_000_000n === 0n;
  } catch {
    return false;
  }
}

/**
 * Returns the times of `at` in scenarios and in the states of contracts that are not an ISO datetime with seconds and an
 * offset, the time form of steps and trace lines, or that have a part below a millisecond.
 */
export function unparsableTimes(
  scenarios: readonly Named<Scenario>[],
  contracts: readonly Contract[],
): Found<Malformed>[] {
  const unparsable = (inputs: Scenario["inputs"]) =>
    inputs.flatMap((input, i) => (input.type === "at" && !readable(input.time) ? [i + 1] : []));
  return [
    ...scenarios.flatMap(({ service, name, place, definition }) =>
      unparsable(definition.inputs).map(
        (input): Found<Malformed> => ({
          violation: {
            kind: "Malformed.unparsableTime",
            definition: null,
            scenario: { service, name },
            input,
            data: {},
          },
          place,
        }),
      ),
    ),
    ...contracts.flatMap(({ service, place, states }) =>
      Object.entries(states).flatMap(([state, inputs]) =>
        unparsable(inputs as StateInputs).map(
          (input): Found<Malformed> => ({
            violation: {
              kind: "Malformed.unparsableTime",
              definition: null,
              input,
              data: { contract: service, state },
            },
            place,
          }),
        ),
      ),
    ),
  ];
}

/**
 * Returns whether the run can add `delay` exactly. The run adds a delay to an instant in whole milliseconds, as Lean's
 * time counts. A date unit has no fixed length for an instant, and parts below a millisecond would be dropped.
 */
function exact(delay: Delay): boolean {
  try {
    const d = Temporal.Duration.from(delay);
    return [d.years, d.months, d.weeks, d.days, d.microseconds, d.nanoseconds].every((n) => n === 0);
  } catch {
    return false;
  }
}

/** Returns the deadlines whose delay the run cannot add exactly; a delay is a value that the chart definition holds. */
export function inexactDelays(
  charts: readonly {
    readonly named: Named<Definition>;
    readonly chart: ChartSpec;
    readonly structure: ChartStructure;
  }[],
): Found<Malformed>[] {
  return charts.flatMap(({ named, chart, structure }) =>
    structure.states.flatMap((state) =>
      Object.entries(stateAt(chart, state.path).after ?? {}).flatMap(([name, deadline]): Found<Malformed>[] =>
        deadline.delay === undefined || exact(deadline.delay)
          ? []
          : [
              {
                violation: {
                  kind: "Malformed.inexactDelay",
                  definition: { service: named.service, name: named.name },
                  data: { state: state.name, deadline: name },
                },
                place: named.place,
              },
            ],
      ),
    ),
  );
}
