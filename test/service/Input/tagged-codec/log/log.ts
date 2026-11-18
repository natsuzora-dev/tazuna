import { emit, service } from "@natsuzora-dev/tazuna";
import { reading } from "./reading.ts";

export const { command, contract, event } = service({ name: "log", description: "Keep the readings" });

export const readingKept = event({ payload: { reading } });

export const record = command({ input: { reading }, emits: [readingKept] }).decide(({ input }) => [
  emit(readingKept, { reading: input.reading }),
]);
