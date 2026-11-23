import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = service({ name: "notifier", description: "Take notifications" });

export const notify = command({ callers: ["client", "todo"], input: { text: z.string() }, emits: [] }).decide(() => []);
