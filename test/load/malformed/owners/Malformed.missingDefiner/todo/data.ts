import { service } from "@natsuzora-dev/tazuna";

const { event } = service({ name: "todo", description: "Keep the notes" });

export const noted = event({});
