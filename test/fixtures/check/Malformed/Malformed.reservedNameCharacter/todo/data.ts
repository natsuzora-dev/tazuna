import { service, unchecked } from "@natsuzora-dev/tazuna";

export const { event } = service(unchecked({ name: "todo.tasks", description: "Keep the tasks" }));

export const taskAdded = event({});
