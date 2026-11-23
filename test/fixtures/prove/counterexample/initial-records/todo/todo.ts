import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Settings = singleEntity({
  description: "The settings",
  fields: { limit: z.int().default(-1) },
  invariants: { nonNegativeLimit: ({ record }) => record.limit >= 0 },
});

export const { command, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the settings",
  entities: { Settings },
});

export const limitChanged = updateEvent({ entity: Settings, writes: ["limit"] });

export const changeLimit = command({
  callers: ["client"],
  input: { limit: z.int().min(0) },
  emits: [limitChanged],
}).decide(({ input }) => [emit(limitChanged, { limit: input.limit })]);

export const todoBounds = bounds({ creates: {} });
