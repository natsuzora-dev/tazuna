import { constants, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event, contract } = service({ name: "todo", description: "Keep the tasks" });

type Tree = { readonly name: string; readonly children: readonly Tree[] };
const tree: z.ZodType<Tree> = z.lazy(() => z.object({ name: z.string(), children: z.array(tree) }));

export const taskAdded = event({
  payload: {
    cents: z.codec(z.string(), z.int(), { decode: Number, encode: String }),
    length: z.string().transform((s) => s.length),
    title: z.string().refine((s) => s !== ""),
    note: z.string().trim(),
    count: z.coerce.number(),
    owner: z.email(),
    code: z.string().regex(/^[A-Z]+$/),
    tags: z.record(z.string(), z.string()),
    point: z.tuple([z.int(), z.int()]),
    tree,
    size: z.int().min(1, { error: (issue) => `at least 1, not ${String(issue.input)}` }),
    named: z.string().min(1, "a name has text"),
    startsWithA: z.string().startsWith("a"),
  },
});

export const todo = contract({ taskAdded });

export const limits = constants({
  service: "todo",
  schema: z.strictObject({ owners: z.record(z.string(), z.int()) }),
  values: { owners: {} },
});
