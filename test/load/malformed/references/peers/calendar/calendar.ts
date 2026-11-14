import { externalService } from "@natsuzora-dev/tazuna";

export const { command } = externalService({ description: "Keep reminders" });

export const addReminder = command({ emits: [], rejects: ["unavailable"] });
