import { emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Mark = entity({ description: "A mark", fields: { id: z.string() }, key: "id" });
export const Flag = singleEntity({ description: "A flag", fields: { isOn: z.boolean().default(false) } });

export const { automation, command, machine, event, createEvent, updateEvent, contract } = service({
  description: "Mark each added task, raise a flag, and notice when there is a mark",
  entities: { Mark, Flag },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const marked = createEvent({ entity: Mark });
export const flagged = updateEvent({ entity: Flag, writes: ["isOn"] });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const mark = command({
  input: { id: z.string() },
  emits: [marked],
}).decide(({ input, records }) => (records.Mark.get(input.id) === undefined ? [emit(marked, { id: input.id })] : []));

export const raise = command({ emits: [flagged] }).decide(() => [emit(flagged, { isOn: true })]);

export const markAdded = automation({
  receives: { taskAdded },
  commands: { mark },
}).send({ input: ({ payload }) => ({ id: payload.id }) });

export const raiseOnAdd = automation({
  receives: { taskAdded },
  commands: { raise },
}).send({});

export const watcher = machine({
  description: "Notice when there is a mark",
  initial: "few",
  states: { few: {}, many: {} },
}).chart({
  states: {
    few: { always: [{ guard: { hasMarks: ({ records }) => records.Mark.size > 0 }, target: "many" }] },
    many: { always: [{ guard: { hasNoMarks: ({ records }) => records.Mark.size === 0 }, target: "few" }] },
  },
});

export const counter = contract({ addTask });
