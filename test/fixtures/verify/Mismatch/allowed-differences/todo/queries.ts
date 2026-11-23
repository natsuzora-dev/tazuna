import { instant, parseInstant } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { query } from "./todo.ts";

const part = z.union([z.strictObject({ name: z.string() }), z.strictObject({ size: z.int() })]);

export const taskCard = query({
  callers: ["client"],
  output: {
    card: z.object({ title: z.string(), detail: z.object({ note: z.string() }) }),
    due: z.strictObject({ at: instant, parts: z.array(z.strictObject({ name: z.string() })) }),
    mark: z.discriminatedUnion("kind", [
      z.strictObject({ kind: z.literal("one"), part }),
      z.strictObject({ kind: z.literal("many"), parts: z.array(part).optional() }),
    ]),
  },
}).resolve(() => ({
  card: { title: "Buy milk", detail: { note: "2 bottles" } },
  due: { at: parseInstant("2026-10-25T01:00:00Z"), parts: [{ name: "morning" }] },
  mark: { kind: "one" as const, part: { name: "store" } },
}));

export const taskNote = query({
  callers: ["client"],
  input: { taskId: z.string() },
  output: { note: z.string() },
  requires: { hasTaskId: ({ input }) => input.taskId !== "" },
}).resolve(() => ({ note: "2 bottles" }));
