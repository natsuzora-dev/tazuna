import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

const nextDay = fulfilled({ day: "2026-10-26T00:00:00+09:00" });

export const chosenByContent = scenario({
  description:
    "Add a task and answer three times; the first answer names the request whose input has from 11:00, calendar.nextDay#3, the second names from 10:00, calendar.nextDay#1, and the third names from 12:00, calendar.nextDay#2; a pick compares the value as the trace writes it, in UTC, and the requests' field constructor, which no pick gives, takes no part in the choice",
  given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    const add = w.client.send(addTask, {});
    const deliverAndAnswer = (from: string) => {
      const request = add.request(calendar.nextDay, { from });
      w.net.deliver(request);
      w.net.deliver(w.peer.calendar.answer(request, nextDay));
    };
    deliverAndAnswer("2026-10-25T02:00:00Z");
    deliverAndAnswer("2026-10-25T01:00:00Z");
    deliverAndAnswer("2026-10-25T03:00:00Z");
  },
  then: () => [],
});
