import { service } from "@natsuzora-dev/tazuna";

export const { event } = service({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({});
