import { bag, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ name: "shelf", description: "Label groups of items" });

const group = z.union([
  z.object({ names: bag(z.string()) }),
  z.object({ names: bag(z.string()), label: z.string().optional() }),
]);

export const grouped = event({ payload: { group } });

export const groupItems = command({ callers: ["client"], emits: [grouped] }).decide(() => [
  emit(grouped, { group: { names: [] } }),
]);
