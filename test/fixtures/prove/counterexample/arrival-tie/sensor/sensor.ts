import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event, contract } = externalService({ name: "sensor", description: "Report readings of a door" });

export const read = event({ payload: { state: z.enum(["open", "closed"]) } });
