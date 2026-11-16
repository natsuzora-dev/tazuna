import { contract, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event } = service({ description: "Close the tasks" });

export const tasksClosed = event({});

export const closeTasks = command({ emits: [tasksClosed] }).decide(() => [emit(tasksClosed, {})]);

export const copyReadsRegion = machine({
  description:
    "Note the closing in state x in one region, and the copy k of map m saves the notes into seen in the other region",
  context: { notes: z.array(z.string()).default([]), seen: z.array(z.string()).default([]) },
  receives: { tasksClosed },
  initial: "open",
  states: {
    open: {
      type: "parallel",
      states: {
        left: {
          initial: "m",
          states: { m: { type: "map", key: { name: z.string() }, initial: "c1", states: { c1: {} } } },
        },
        right: { initial: "x", states: { x: {}, y: {} } },
      },
    },
  },
}).chart({
  states: {
    m: { items: () => [{ name: "k" }] },
    c1: { on: { tasksClosed: [{ assign: { seen: ({ context }) => [...context.notes] } }] } },
    x: { on: { tasksClosed: [{ target: "y", assign: { notes: ({ context }) => [...context.notes, "x"] } }] } },
    y: { on: { tasksClosed: [{ target: "x" }] } },
  },
});

export const closer = contract({ closeTasks });
