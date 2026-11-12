import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine } = service({ description: "Book the days" });

export const booker = machine({
  description: "Book now",
  commands: { book: calendar.book },
  initial: "booking",
  states: { booking: {}, done: { type: "final" } },
}).chart({
  states: {
    booking: {
      sends: {
        book: {
          input: ({ now }) => ({ day: now }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
