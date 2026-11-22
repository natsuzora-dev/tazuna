import { parseInstant } from "@natsuzora-dev/tazuna";
import { clearAll, given, scenario } from "./reminders.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] });

export const eventWithoutKeyFields = scenario({
  description: "Clear all; allCleared, whose payload has no taskId, reaches every copy",
  given: arranged,
  when: (w) => {
    w.client.send(clearAll, {});
  },
  then: () => [],
});
