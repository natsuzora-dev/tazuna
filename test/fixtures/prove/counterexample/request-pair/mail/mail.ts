import { externalService } from "@natsuzora-dev/tazuna";

export const { command, contract } = externalService({
  name: "mail",
  description: "Send a notice",
});

export const notify = command({ callers: ["board"], emits: [], rejects: [] });
