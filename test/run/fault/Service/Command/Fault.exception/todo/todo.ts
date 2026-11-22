import { addDays, date, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract, scenario } = service({ name: "todo", description: "Log the titles of tasks" });

export const titleLogged = event({ payload: { title: z.string(), until: date } });

export const logTitle = command({ input: { title: z.string(), from: date }, emits: [titleLogged] }).decide(
  ({ input }) => [emit(titleLogged, { title: input.title, until: addDays(input.from, 3_000_000) })],
);

export const todo = contract({ logTitle });
