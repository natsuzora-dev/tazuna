import { arm, scenario } from "./marks.ts";

export const tied = scenario({
  description:
    "Arm at 09:00 and move the clock to 11:00; the deadlines of first and second tie at 10:00, and each adds four marks whose only field is a created key and counts them, so comparing the records of the two orders tries more renamings than bindingLimit and test reports stepOrderBindings",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Mark: [], Count: { n: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(arm, {});
    w.clock.at("2026-10-25T11:00:00+09:00");
  },
  then: () => [],
});
