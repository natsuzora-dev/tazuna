import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), points: z.int() }, key: "id" });

export const { screen, scenario } = service({
  name: "throwingOpensInput",
  description: "Open a picker with an input whose sum faults",
  entities: { Task },
});

export const pickScreen = screen({
  description: "Pick a number below the count",
  input: { count: z.int() },
  initial: "picking",
  states: { picking: {} },
}).chart({});

export const homeScreen = screen({
  description: "Open the picker",
  screens: { pickScreen },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
}).chart({
  states: {
    picking: {
      opens: {
        pickScreen: {
          modal: true,
          input: ({ records }) => ({ count: records.Task.sum((task) => task.points) }),
          onDone: [{ target: "done" }],
        },
      },
    },
  },
});
