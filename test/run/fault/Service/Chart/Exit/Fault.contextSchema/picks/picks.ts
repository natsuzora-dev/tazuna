import { service, set } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine, scenario } = service({ name: "picks", description: "Keep the picked tags" });

export const picker = machine({
  description: "Pick tags when the service starts",
  context: { picked: set(z.string()).default([]) },
  initial: "picking",
  states: { picking: {} },
}).chart({ states: { picking: { entry: { assign: { picked: () => ["a", "a"] } } } } });
