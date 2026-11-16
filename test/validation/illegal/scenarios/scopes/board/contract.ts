import { at, contract, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { shown } from "./board.ts";

export const watchingBoard = subscribe(shown, {});

export const board = contract({
  shown,
  states: {
    endsUnopened: [at("2026-10-25T09:00:00+09:00"), unsubscribe(watchingBoard)],
    watched: [at("2026-10-25T09:00:00+09:00"), watchingBoard],
  },
});
