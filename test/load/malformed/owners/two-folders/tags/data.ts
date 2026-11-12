import { service } from "@natsuzora-dev/tazuna";

export const { event } = service({ description: "Keep the tags" });

export const tagAdded = event({});
