import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract, scenario } = service({ name: "todo", description: "Keep the titles" });

export const rename = command({
  input: {
    title: z.string().refine((title) => {
      if (title === "a") throw new Error("a is no title");
      return true;
    }),
  },
  emits: [],
}).decide(() => []);

export const todo = contract({ rename });
