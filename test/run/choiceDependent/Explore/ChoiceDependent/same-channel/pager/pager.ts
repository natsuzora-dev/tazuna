import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "pager", description: "Page a person" });

export const page = command({ input: { by: z.string() }, emits: [], rejects: [] });
