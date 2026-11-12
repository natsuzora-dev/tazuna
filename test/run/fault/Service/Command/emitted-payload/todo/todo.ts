import { contract, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ description: "Log the titles of tasks" });

export const titleLogged = event({
  payload: {
    title: z.string().refine((title) => {
      if (title === "") throw new Error("a logged title needs text");
      return true;
    }),
  },
});

export const logTitle = command({ input: { title: z.string() }, emits: [titleLogged] }).decide(({ input }) => [
  emit(titleLogged, { title: input.title }),
]);

export const todo = contract({ logTitle });
