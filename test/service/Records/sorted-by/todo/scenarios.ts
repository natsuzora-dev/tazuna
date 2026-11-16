import { at, operate, scenario, send } from "@natsuzora-dev/tazuna";
import { checkPlan, listTasks, listVisits, pickScreen, planScreen, planTasks } from "./todo.ts";

export const listed = scenario(
  "List the tasks; decide writes the titles and the entries of tasksListed out of order, and tazuna sorts the titles bag by canonical JSON and the entries by day, the two entries of day 1 by canonical JSON",
  [at("2026-10-25T10:00:00+09:00"), send(listTasks, {})],
);

export const sortedInSpec = scenario(
  "Fill and open planScreen and finish pickScreen; the assign of fill of planScreen and the resolve of pickScreen write entries out of day order, but tazuna sorts the context and the output by day, so the invariants of planScreen and the ensures of pickScreen hold",
  [
    at("2026-10-25T10:00:00+09:00"),
    operate(planScreen, "fill"),
    operate(planScreen, "open"),
    operate(pickScreen, "finish"),
  ],
);

export const unsortedInput = scenario(
  "Plan tasks with entries out of day order and then in day order; the first planTasks does not fit the input schema and is rejected with invalid-input, and the second is accepted",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(planTasks, {
      entries: [
        { day: 2, title: "Buy eggs" },
        { day: 1, title: "Buy milk" },
      ],
    }),
    send(planTasks, {
      entries: [
        { day: 1, title: "Buy milk" },
        { day: 2, title: "Buy eggs" },
      ],
    }),
  ],
);

export const listedByTime = scenario(
  "List the visits; decide writes the visits in one order to byTime and byDay of visitsListed, and tazuna sorts byTime by the time at and byDay by the date on",
  [at("2026-10-25T10:00:00+09:00"), send(listVisits, {})],
);

export const nullableSorted = scenario(
  "Check the plan unfilled and filled; nullable and union of planChecked hold null or entries in day order. tazuna writes null as it is and sorts the entries by day",
  [at("2026-10-25T10:00:00+09:00"), send(checkPlan, { isFilled: false }), send(checkPlan, { isFilled: true })],
);
