import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, scenario } = service({ description: "Book days" });

export const booker = machine({
  description: "Book the day when the service starts",
  commands: { book: calendar.book },
  initial: "booking",
  states: { booking: {}, booked: { type: "final" } },
}).chart({
  states: {
    booking: {
      sends: {
        book: {
          input: ({ now }) => ({ day: now }),
          onAccepted: [{ target: "booked" }],
          onRejected: [{ target: "booked" }],
        },
      },
    },
  },
});
