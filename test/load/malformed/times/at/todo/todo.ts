import { at, call, contract, scenario, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query } = service({ description: "Answer the task count" });

export const taskCount = query({ output: { count: z.int() } }).resolve(() => ({ count: 0 }));

export const todo = contract({ taskCount });

export const countAtEachTime = scenario(
  "Count at a time without an offset, at a time without seconds, at a time with ten fraction digits, at a time with a part below a millisecond, and at a time with zeros below a millisecond",
  [
    at("2026-10-25T09:00:00"),
    call(taskCount, {}),
    at("2026-10-25T09:01+09:00"),
    call(taskCount, {}),
    at("2026-10-25T09:02:00.1234567891+09:00"),
    call(taskCount, {}),
    at("2026-10-25T09:03:00.0009+09:00"),
    call(taskCount, {}),
    at("2026-10-25T09:04:00.001000+09:00"),
    call(taskCount, {}),
  ],
);
