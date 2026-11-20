import { service } from "@natsuzora-dev/tazuna";
import { dueTasks } from "../dueTasks/tasks.ts";

export const { screen, scenario } = service({ name: "stampedBoard", description: "Show the tasks due soon" });

const by: Temporal.Instant = JSON.parse('"2026-10-26T00:00:00Z"');

export const board = screen({
  description: "The number of tasks due by a time that it holds as the text of an Instant",
  queries: { dueBy: dueTasks.dueBy },
  initial: "showing",
  states: { showing: {} },
}).chart({
  states: { showing: { shows: { dueBy: { input: () => ({ by }) } } } },
});
