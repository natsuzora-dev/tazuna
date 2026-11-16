import { externalService } from "@natsuzora-dev/tazuna";

export const { query, contract } = externalService({ description: "Return the next business day" });
