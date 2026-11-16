import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Seen = entity({ description: "A task the service saw", fields: { id: z.string() }, key: "id" });

export const { automation, command, createEvent, event, contract } = service({
  description: "See each added task",
  entities: { Seen },
});

export const taskAdded = event({ payload: { taskId: z.string() } });
export const seenRecorded = createEvent({ entity: Seen });
export const seen = event({ payload: { id: ref(Seen) } });

export const addTasks = command({
  input: { taskIds: z.array(z.string()) },
  emits: [taskAdded],
}).decide(({ input }) => input.taskIds.map((taskId) => emit(taskAdded, { taskId })));

export const see = command({
  input: { id: Seen.fields.id },
  emits: [seenRecorded, seen],
}).decide(({ input }) => [emit(seenRecorded, input), emit(seen, input)]);

export const seeAdded = automation({
  receives: { taskAdded },
  commands: { see },
}).send({ input: ({ createKey }) => ({ id: createKey(ref(Seen)) }) });

export const todo = contract({ addTasks, seen });
