import { any } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const taskListScreen = screen({
  description: "A screen that shows the list of open tasks",
  queries: { tasks: todo.tasks },
  controls: { close: { label: "Close" } },
  initial: "showing",
  states: { showing: {}, closed: { type: "final" } },
}).chart({
  offers: { close: any },
  states: {
    showing: { on: { close: [{ target: "closed" }] }, shows: { tasks: { input: () => ({ filter: "open" }) } } },
  },
});

export const helpPanel = screen({
  description: "The help, which opens beside the home screen",
  controls: { closeHelp: { label: "Close help" } },
  initial: "showing",
  states: { showing: {}, closed: { type: "final" } },
}).chart({ offers: { closeHelp: any }, states: { showing: { on: { closeHelp: [{ target: "closed" }] } } } });

export const homeScreen = screen({
  description: "A home screen that shows the task count and opens the task list for one minute or the help",
  context: { filter: z.enum(["open", "all"]).default("open") },
  queries: { taskCount: todo.taskCount },
  screens: { taskList: taskListScreen, help: helpPanel },
  controls: {
    openList: { label: "Open list" },
    openHelp: { label: "Help" },
    countAll: { label: "Count all" },
  },
  initial: "open",
  states: { open: { initial: "home", states: { home: {}, listing: { after: ["minute"] }, helping: {} } } },
}).chart({
  offers: { openList: any, openHelp: any, countAll: any },
  states: {
    open: {
      on: { countAll: [{ assign: { filter: () => "all" } }] },
      shows: { taskCount: { input: ({ context }) => ({ filter: context.filter }) } },
    },
    home: { on: { openList: [{ target: "listing" }], openHelp: [{ target: "helping" }] } },
    listing: {
      after: { minute: { delay: { minutes: 1 }, onFired: [{ target: "home" }] } },
      opens: { taskList: { modal: true, onDone: [{ target: "home" }] } },
    },
    helping: { opens: { help: { modal: false, onDone: [{ target: "home" }] } } },
  },
});
