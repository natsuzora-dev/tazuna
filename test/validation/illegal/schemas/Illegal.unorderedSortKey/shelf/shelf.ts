import { emit, service, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ name: "shelf", description: "List shelves by rank" });

export const shelvesListed = event({
  payload: { shelves: sortedBy(z.object({ name: z.string(), rank: z.int().default(0) }), "rank") },
});

export const listShelves = command({ emits: [shelvesListed] }).decide(() => [emit(shelvesListed, { shelves: [] })]);
