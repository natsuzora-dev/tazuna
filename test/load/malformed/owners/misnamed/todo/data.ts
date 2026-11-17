import { service } from "@natsuzora-dev/tazuna";

export const { event } = service({ name: "tasks", description: "Keep the tasks, named other than the folder todo" });

export const taskNoted = event({});
