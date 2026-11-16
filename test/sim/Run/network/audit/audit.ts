import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, contract } = service({ description: "Follow calendar's confirmations" });

export const confirmations = machine({
  description: "Take calendar's confirmations",
  receives: { bookingConfirmed: calendar.bookingConfirmed },
  initial: "following",
  states: { following: {} },
}).chart({ states: { following: { on: { bookingConfirmed: [{ target: "following" }] } } } });
