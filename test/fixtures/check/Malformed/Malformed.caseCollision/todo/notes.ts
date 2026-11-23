import { service } from "@natsuzora-dev/tazuna";

export const { event } = service({ name: "Todo", description: "Keep the notes" });

export const noteAdded = event({});
