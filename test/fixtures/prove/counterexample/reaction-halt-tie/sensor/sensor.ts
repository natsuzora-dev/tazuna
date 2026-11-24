import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event, contract } = externalService({ name: "sensor", description: "Report readings" });

export const read = event({ payload: { kind: z.enum(["set", "check"]) } });
