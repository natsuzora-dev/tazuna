import { emit, entity, parseInstant, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Mark = entity({ description: "A mark", fields: { id: z.string() }, key: "id" });

export const Count = singleEntity({ description: "Marks added", fields: { n: z.int().default(0) } });

export const { command, machine, event, createEvent, updateEvent, contract, scenario } = service({
  name: "marks",
  description: "Add four marks and count them from each of two clocks at 10:00",
  entities: { Mark, Count },
});

export const armed = event({});
export const marked = createEvent({ entity: Mark });
export const counted = updateEvent({ entity: Count, writes: ["n"] });

export const arm = command({ callers: ["client"], emits: [armed] }).decide(() => [emit(armed, {})]);

const key = Mark.fields.id;

export const addMarks = command({
  callers: ["client", "marks"],
  input: { a: key, b: key, c: key, d: key },
  emits: [marked, counted],
}).decide(({ input, records }) => [
  emit(marked, { id: input.a }),
  emit(marked, { id: input.b }),
  emit(marked, { id: input.c }),
  emit(marked, { id: input.d }),
  emit(counted, { n: records.Count.n + 4 }),
]);

const clock = (name: string) =>
  machine({
    description: `Add four marks at 10:00 once armed (${name})`,
    receives: { armed },
    commands: { addMarks },
    initial: "idle",
    states: { idle: {}, waiting: {}, marking: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "waiting" }] } },
      waiting: {
        after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "marking" }] } },
      },
      marking: {
        sends: {
          addMarks: {
            input: ({ createKey }) => ({
              a: createKey(ref(Mark)),
              b: createKey(ref(Mark)),
              c: createKey(ref(Mark)),
              d: createKey(ref(Mark)),
            }),
            onAccepted: [{ target: "done" }],
            onRejected: [{ target: "done" }],
          },
        },
      },
    },
  });

export const first = clock("first");
export const second = clock("second");

export const marks = contract({ arm });
