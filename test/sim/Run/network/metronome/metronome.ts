import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Beat = entity({ description: "A beat to mark", fields: { id: z.string() }, key: "id" });

export const { command, contract, createEvent, event, machine } = service({
  name: "metronome",
  description: "Beat tick, tock, tick, and mark each beat from its own copy",
  entities: { Beat },
});

export const tick = event({});
export const tock = event({});
export const beatAdded = createEvent({ entity: Beat });
export const marked = event({ payload: { beatId: z.string() } });

export const beat = command({ emits: [tick, tock] }).decide(() => [emit(tick, {}), emit(tock, {}), emit(tick, {})]);

export const addBeats = command({ input: { beatIds: z.array(Beat.fields.id) }, emits: [beatAdded] }).decide(
  ({ input }) => input.beatIds.map((id) => emit(beatAdded, { id })),
);

export const mark = command({ input: { beatId: ref(Beat) }, emits: [marked] }).decide(({ input }) => [
  emit(marked, { beatId: input.beatId }),
]);

export const marker = machine({
  description: "Mark once from the copy of each beat",
  commands: { mark },
  initial: "beats",
  states: {
    beats: { type: "map", key: { beatId: ref(Beat) }, initial: "marking", states: { marking: {}, done: {} } },
  },
}).chart({
  states: {
    beats: { items: ({ records }) => records.Beat.map((b) => ({ beatId: b.id })) },
    marking: { sends: { mark: { input: ({ key }) => key, onAccepted: [{ target: "done" }], onRejected: [] } } },
  },
});
