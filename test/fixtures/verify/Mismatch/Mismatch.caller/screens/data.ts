import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Draft = entity({ description: "A draft note", fields: { id: z.string() }, key: "id" });

export const { screen, given, scenario, contract } = service({
  name: "screens",
  description: "Show the links between notes",
  entities: { Draft },
});
