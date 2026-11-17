import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({
  name: "closer",
  description: "Close the tasks",
});

export const tasksClosed = event({});

export const closeTasks = command({ emits: [tasksClosed] }).decide(() => [emit(tasksClosed, {})]);

export const copyAndRegion = machine({
  description: "Note the closing in the copy k of map m in one region and in state x in the other",
  context: { notes: z.array(z.string()).default([]) },
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
    c1: { on: { tasksClosed: [{ assign: { notes: ({ context, key }) => [...context.notes, `copy ${key.name}`] } }] } },
    x: { on: { tasksClosed: [{ target: "y", assign: { notes: ({ context }) => [...context.notes, "x"] } }] } },
    y: { on: { tasksClosed: [{ target: "x" }] } },
  },
});

export const copiesOfTwoMaps = machine({
  description: "Note the closing in the copy k of map m in one region and in the copy k of map m2 in the other",
  context: { notes: z.array(z.string()).default([]) },
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
        right: {
          initial: "m2",
          states: { m2: { type: "map", key: { name: z.string() }, initial: "c2", states: { c2: {} } } },
        },
      },
    },
  },
}).chart({
  states: {
    m: { items: () => [{ name: "k" }] },
    m2: { items: () => [{ name: "k" }] },
    c1: { on: { tasksClosed: [{ assign: { notes: ({ context }) => [...context.notes, "c1"] } }] } },
    c2: { on: { tasksClosed: [{ assign: { notes: ({ context }) => [...context.notes, "c2"] } }] } },
  },
});

export const twoCopies = machine({
  description: "Note the closing in each of the copies k and l of map m",
  context: { notes: z.array(z.string()).default([]) },
  receives: { tasksClosed },
  initial: "m",
  states: { m: { type: "map", key: { name: z.string() }, initial: "c1", states: { c1: {} } } },
}).chart({
  states: {
    m: { items: () => [{ name: "k" }, { name: "l" }] },
    c1: { on: { tasksClosed: [{ assign: { notes: ({ context, key }) => [...context.notes, `copy ${key.name}`] } }] } },
  },
});

export const closer = contract({ closeTasks });
