import { run } from "@natsuzora-dev/tazuna";
import { log } from "../log/contract.ts";
import { given, scenario, takeReading } from "./todo.ts";

const arranged = given({ start: "2026-10-25T09:00:00+09:00", records: {}, peers: [run(log, {})] });

export const fahrenheitReading = scenario(
  "Take a reading of 81 degrees Fahrenheit; readingSent sends record with the reading, which todo writes and log records in its unit and with its time, each written back by the codec of the option that the tag names. The celsius option also encodes 300 kelvin, as 27, so a plain union would leave the option to a guess, and check requires the tag",
  {
    given: arranged,
    when: (w) => {
      const taken = w.client.send(takeReading, {
        reading: { unit: "fahrenheit", kelvin: 81, at: "2026-10-25T09:00:00+09:00" },
      });
      const recorded = w.net.deliver(taken.request(log.record));
      w.net.deliver(recorded.answer(recorded));
    },
    then: () => [],
  },
);
