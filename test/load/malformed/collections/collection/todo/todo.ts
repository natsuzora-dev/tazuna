import { bag, constants, service, set, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = service({ name: "todo", description: "Answer the marks" });

export const marksWithVisibleCollections = query({
  output: {
    tags: bag(z.string()).default([]),
    days: z.array(sortedBy(z.strictObject({ n: z.int() }), "n")).optional(),
    ids: z.union([set(z.string()), z.null()]),
  },
}).resolve(() => ({ tags: [], days: [], ids: null }));

export const marks = query({
  output: {
    tags: z.record(z.string(), bag(z.string())),
    days: z.tuple([sortedBy(z.strictObject({ n: z.int() }), "n")]),
    ids: set(z.string()).readonly(),
  },
}).resolve(() => ({ tags: {}, days: [[{ n: 1 }]], ids: [] }));

export const todo = contract({ marksWithVisibleCollections, marks });

export const defaults = constants(z.strictObject({ days: z.tuple([set(z.string())]) }), { days: [[]] });
