import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine, scenario } = service({ name: "levels", description: "Keep a level from 0 to 2" });

export const meter = machine({
  description: "Raise the level past its maximum when the service starts",
  context: { level: z.int().min(0).max(2).default(0) },
  initial: "raising",
  states: { raising: {} },
}).chart({ states: { raising: { entry: { assign: { level: ({ context }) => context.level + 3 } } } } });
