import {
  checkPlan,
  given,
  listPrices,
  listTasks,
  listVisits,
  pickScreen,
  planScreen,
  planTasks,
  scenario,
} from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] });

export const listed = scenario({
  description:
    "List the tasks; decide writes the titles and the entries of tasksListed out of order, and tazuna sorts the titles bag by canonical JSON and the entries by day, the two entries of day 1 by canonical JSON",
  given: arranged,
  when: (w) => {
    w.client.send(listTasks, {});
  },
  then: () => [],
});

export const sortedInSpec = scenario({
  description:
    "Fill and open planScreen and finish pickScreen; the assign of fill of planScreen and the resolve of pickScreen write entries out of day order, but tazuna sorts the context and the output by day, so the invariants of planScreen and the ensures of pickScreen hold",
  given: arranged,
  when: (w) => {
    const plan = w.startup.screen(planScreen);
    w.user.operate(plan, "fill");
    const open = w.user.operate(plan, "open");
    w.user.operate(open.screen(pickScreen), "finish");
  },
  then: () => [],
});

export const unsortedInput = scenario({
  description:
    "Plan tasks with entries out of day order and then in day order; the first planTasks does not fit the input schema and is rejected with invalid-input, and the second is accepted",
  given: arranged,
  when: (w) => {
    w.client.send(planTasks, {
      entries: [
        { day: 2, title: "Buy eggs" },
        { day: 1, title: "Buy milk" },
      ],
    });
    w.client.send(planTasks, {
      entries: [
        { day: 1, title: "Buy milk" },
        { day: 2, title: "Buy eggs" },
      ],
    });
  },
  then: () => [],
});

export const listedByTime = scenario({
  description:
    "List the visits; decide writes the visits in one order to byTime and byDay of visitsListed, and tazuna sorts byTime by the time at and byDay by the date on",
  given: arranged,
  when: (w) => {
    w.client.send(listVisits, {});
  },
  then: () => [],
});

export const nullableSorted = scenario({
  description:
    "Check the plan unfilled and filled; nullable and union of planChecked hold null or entries in day order. tazuna writes null as it is and sorts the entries by day",
  given: arranged,
  when: (w) => {
    w.client.send(checkPlan, { isFilled: false });
    w.client.send(checkPlan, { isFilled: true });
  },
  then: () => [],
});

export const listedPrices = scenario({
  description:
    'List the prices; decide writes 150 and 20 cents, and tazuna sorts the prices bag by the canonical JSON of the encoded values, so "0.20" comes before "1.50"',
  given: arranged,
  when: (w) => {
    w.client.send(listPrices, {});
  },
  then: () => [],
});
