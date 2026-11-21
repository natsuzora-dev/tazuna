import { datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { takeReading } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(takeReading.input.reading.options[0].shape.kelvin, [81]),
    domain(takeReading.input.reading.options[1].shape.kelvin, [0]),
    domain(datetime, ["2026-10-25T09:00:00+09:00"]),
  ],
});
