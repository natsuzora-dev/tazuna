import { any, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "Whether a panel claimed the board",
  fields: { used: z.boolean().default(false) },
});

export const { command, screen, event, updateEvent, contract, scenario } = service({
  name: "panels",
  description: "Two panels each open a detail in either order, then a third panel opens one more",
  entities: { Board },
});

export const ready = event({});
export const claimed = updateEvent({ entity: Board, writes: ["used"] });

export const announce = command({ emits: [ready] }).decide(() => [emit(ready, {})]);
export const claim = command({ emits: [claimed] }).decide(() => [emit(claimed, { used: true })]);

export const detailScreen = screen({
  description: "A detail that closes",
  controls: { close: { label: "Close" } },
  initial: "showing",
  states: { showing: {}, closed: { type: "final" } },
}).chart({ offers: { close: any }, states: { showing: { on: { close: [{ target: "closed" }] } } } });

const panel = (side: string) =>
  screen({
    description: `The ${side} panel: on ready it claims the board, then opens a detail screen`,
    receives: { ready },
    commands: { claim },
    screens: { detailScreen },
    initial: "idle",
    states: { idle: {}, claiming: {}, open: {} },
  }).chart({
    states: {
      idle: { on: { ready: [{ target: "claiming" }] } },
      claiming: { sends: { claim: { onAccepted: [{ target: "open" }], onRejected: [] } } },
      open: { opens: { detailScreen: { modal: false, onDone: [] } } },
    },
  });

export const leftPanel = panel("left");
export const rightPanel = panel("right");

export const thirdPanel = screen({
  description: "A panel that opens a detail when the user asks",
  screens: { detailScreen },
  controls: { show: { label: "Show" } },
  initial: "idle",
  states: { idle: {}, open: {} },
}).chart({
  offers: { show: any },
  states: {
    idle: { on: { show: [{ target: "open" }] } },
    open: { opens: { detailScreen: { modal: false, onDone: [] } } },
  },
});

export const panels = contract({ announce });
