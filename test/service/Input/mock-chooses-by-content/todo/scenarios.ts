import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

const nextDay = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const chosenByContent = scenario(
  "Add a task and answer three times; the first answer names the request whose input has from 11:00, calendar.nextDay#3, the second names from 10:00, calendar.nextDay#1, and the third names from 12:00, calendar.nextDay#2; a pick compares the value as the trace writes it, in UTC, and the requests' field constructor, which no pick gives, takes no part in the choice",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      const add = w.client.send(addTask, {});
      const at = (from: string) => add.request(calendar.nextDay, { input: { from } });
      w.peer.calendar.answer(at("2026-10-25T02:00:00Z"), nextDay);
      w.peer.calendar.answer(at("2026-10-25T01:00:00Z"), nextDay);
      w.peer.calendar.answer(at("2026-10-25T03:00:00Z"), nextDay);
    },
    then: () => [],
  },
);
