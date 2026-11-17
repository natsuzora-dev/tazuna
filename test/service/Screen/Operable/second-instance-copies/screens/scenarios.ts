import { offered } from "@natsuzora-dev/tazuna";
import { board, panel, scenario } from "./screens.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} } as const;

export const bumpSecondPanel = scenario(
  "Open two panels and bump row b of the second; the copies of the second panel's rows read their own key and context; no violation",
  {
    given,
    when: (w) => {
      const boardScreen = w.startup.screen(board);
      w.user.operate(boardScreen, "openLeft");
      const right = w.user.operate(boardScreen, "openRight").screen(panel);
      w.user.operate(right, "bump", { row: "b" });
      return { looked: w.user.look(right) };
    },
    then: ({ looked }) => [offered(looked, "bump", { row: "a" })],
  },
);
