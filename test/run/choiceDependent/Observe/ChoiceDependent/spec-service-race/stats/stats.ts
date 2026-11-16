import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Stats = singleEntity({
  description: "Statistics of tasks",
  fields: { completed: z.number().default(0), isCounting: z.boolean().default(true) },
});

export const { command, updateEvent, contract } = service({ description: "Keep the statistics", entities: { Stats } });

export const completedCounted = updateEvent({
  entity: Stats,
  writes: ["completed"],
});

export const countingResumed = updateEvent({
  entity: Stats,
  writes: ["isCounting"],
});

export const countReset = updateEvent({
  entity: Stats,
  writes: ["completed"],
});

export const countCompleted = command({
  emits: [completedCounted],
  requires: { isCounting: ({ records }) => records.Stats.isCounting },
}).decide(({ records }) => [emit(completedCounted, { completed: records.Stats.completed + 1 })]);

export const resumeCounting = command({
  emits: [countingResumed],
}).decide(() => [emit(countingResumed, { isCounting: true })]);

export const resetCount = command({
  emits: [countReset],
}).decide(() => [emit(countReset, { completed: 0 })]);
