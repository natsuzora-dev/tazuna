import { calendar } from "../calendar/contract.ts";
import { screen } from "./data.ts";

const from = () => ({ from: Temporal.Instant.from("2026-10-25T00:00:00Z") });

export const dayScreen = screen({
  description: "Show the next day, and on check show it once more with the same input",
  queries: { nextDay: calendar.nextDay, again: calendar.nextDay },
  controls: { check: { label: "Check" } },
  initial: "open",
  states: { open: { initial: "idle", states: { idle: {}, checking: {} } } },
}).chart({
  states: {
    open: { shows: { nextDay: { input: from } } },
    idle: { on: { check: [{ target: "checking" }] } },
    checking: { on: { check: [{ target: "idle" }] }, shows: { again: { input: from } } },
  },
});
