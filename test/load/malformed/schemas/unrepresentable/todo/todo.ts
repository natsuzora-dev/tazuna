import { constants, datetime, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event, contract } = service({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({
  payload: {
    at: datetime,
    count: z.bigint(),
    tags: z.set(z.string()),
    owners: z.map(z.string(), z.string()),
    ratio: z.nan().optional(),
    mark: z.symbol(),
    length: z.string().transform((s) => s.length),
    trimmed: z.string().pipe(z.string().trim()),
    seen: z.date(),
  },
});

export const todo = contract({ taskAdded });

export const limits = constants("todo", z.strictObject({ most: z.bigint() }), { most: 3n });
