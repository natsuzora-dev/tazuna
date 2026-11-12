import { service } from "@natsuzora-dev/tazuna";

export const { event } = service({ description: "Keep the tasks" });

export const taskAdded = event({});
