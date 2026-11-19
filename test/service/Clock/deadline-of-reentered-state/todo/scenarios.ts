import { addTask, scenario } from "./todo.ts";

export const deadlineOfReenteredState = scenario(
  "Add a task at 10:00; reminder enters waiting with an 11:00 deadline. At 11:00, before it processes that deadline, reminder reenters active through an always transition, so it exits waiting, which cancels the 11:00 deadline, and reenters waiting with a 12:00 deadline. The canceled 11:00 deadline does not reach the reentered waiting, so reminder reports at 12:00",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] },
    when: (w) => {
      w.client.send(addTask, {});
      w.clock.at("2026-10-25T13:00:00+09:00");
    },
    then: () => [],
  },
);
