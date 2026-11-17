import { emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });
export const Board = singleEntity({ description: "The board of the tasks", fields: { title: z.string().default("") } });

export const { command, query, machine, event, createEvent, contract, scenario } = service({
  name: "tasks",
  description: "Two clocks each add a task at 10:00",
  entities: { Task, Board },
});

export const armed = event({});
export const taskAdded = createEvent({ entity: Task });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const title = query({
  output: { title: Board.fields.title },
}).resolve(({ records }) => ({ title: records.Board.title }));

const clock = (id: string) =>
  machine({
    description: `Add task ${id} at 10:00 once armed`,
    receives: { armed },
    commands: { addTask },
    initial: "idle",
    states: { idle: {}, waiting: {}, adding: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "waiting" }] } },
      waiting: {
        after: { due: { at: () => Temporal.Instant.from("2026-10-25T01:00:00Z"), onFired: [{ target: "adding" }] } },
      },
      adding: {
        sends: {
          addTask: {
            input: () => ({ taskId: id }),
            onAccepted: [{ target: "done" }],
            onRejected: [{ target: "done" }],
          },
        },
      },
    },
  });

export const first = clock("a");
export const second = clock("b");

export const tasks = contract({ arm, title });
