import { service } from "@natsuzora-dev/tazuna";

export const { command } = service({ name: "todo", description: "Track the user's tasks" });

export const taskLimit: number = "ten";
