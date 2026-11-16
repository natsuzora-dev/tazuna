import { scenario } from "./screens.ts";

export const start = scenario(
  "Start the service; the opens input of homeScreen for pickScreen throws, so test reports exception of homeScreen",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (_w) => {},
    then: () => [],
  },
);
