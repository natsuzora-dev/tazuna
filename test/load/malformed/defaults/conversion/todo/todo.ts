import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task, whose title default throws",
  fields: {
    id: z.string(),
    title: z.string().default(() => {
      throw new Error("no title is set");
    }),
  },
  key: "id",
});

export const { command, createEvent, event } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const noteAdded = event({ payload: { text: z.string() } });

export const addTask = command({
  input: { taskId: z.string(), title: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const addNote = command({
  input: {
    text: z.string().default(() => {
      throw new Error("no text is set");
    }),
  },
  emits: [noteAdded],
}).decide(({ input }) => [emit(noteAdded, { text: input.text })]);
