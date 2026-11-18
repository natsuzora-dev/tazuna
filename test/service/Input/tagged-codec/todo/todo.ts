import { emit, service } from "@natsuzora-dev/tazuna";
import { log } from "../log/contract.ts";
import { reading } from "../log/reading.ts";

export const { automation, command, event, contract, scenario } = service({
  name: "todo",
  description: "Keep the list",
});

export const readingTaken = event({ payload: { reading } });

export const takeReading = command({ input: { reading }, emits: [readingTaken] }).decide(({ input }) => [
  emit(readingTaken, input),
]);

export const readingSent = automation({
  receives: { readingTaken },
  commands: { record: log.record },
}).send({ input: ({ payload }) => ({ reading: payload.reading }), onRejected: [] });
