import type { Delay } from "../data/datetime.ts";
import type { Malformed } from "../data/malformed.ts";
import { stateAt } from "../dsl/chart.ts";
import type { ChartSpec, Definition, Named } from "../dsl/definition.ts";
import type { ChartStructure } from "../syntax/structure.ts";
import type { Found } from "./found.ts";

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
