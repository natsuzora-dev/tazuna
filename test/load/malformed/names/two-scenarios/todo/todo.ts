import { service } from "@natsuzora-dev/tazuna";

export const { event, scenario } = service({ description: "Keep the tasks" });

export const taskAdded = event({});
