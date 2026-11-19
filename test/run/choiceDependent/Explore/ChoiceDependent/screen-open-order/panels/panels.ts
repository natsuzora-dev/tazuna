import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "Whether a panel claimed the board",
  fields: { used: z.boolean().default(false) },
});

export const { command, screen, event, updateEvent, contract, scenario } = service({
  name: "panels",
  description: "Two panels each claim the board and then open a detail screen",
  entities: { Board },
});

export const ready = event({});
export const claimed = updateEvent({ entity: Board, writes: ["used"] });

export const announce = command({ emits: [ready] }).decide(() => [emit(ready, {})]);
export const claim = command({ emits: [claimed] }).decide(() => [emit(claimed, { used: true })]);

export const detailScreen = screen({
  description: "Show which panel opened it",
  input: { side: z.string() },
  context: { side: z.string() },
  initial: "showing",
  states: { showing: {} },
}).chart({ initialContext: ({ input }) => ({ side: input.side }) });

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
      open: { opens: { detailScreen: { modal: false, input: () => ({ side }), onDone: [] } } },
    },
  });

export const leftPanel = panel("left");
export const rightPanel = panel("right");

export const panels = contract({ announce });
