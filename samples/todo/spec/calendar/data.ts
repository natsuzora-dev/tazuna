import { externalService } from "@natsuzora-dev/tazuna";

export const { query, contract } = externalService({ name: "calendar", description: "Return the next business day" });
