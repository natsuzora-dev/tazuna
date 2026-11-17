import { service } from "@natsuzora-dev/tazuna";

export const { event } = service({ name: "tags", description: "Keep the tags" });

export const tagAdded = event({});
