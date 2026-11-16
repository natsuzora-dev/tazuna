import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ description: "Search the tasks" });

export const searchScreen = screen({
  description: "Search with a query",
  controls: {
    search: {
      label: "Search",
      payload: {
        query: z.string().refine((query) => {
          if (query === "") throw new Error("a search needs a query");
          return true;
        }),
      },
    },
  },
  initial: "searching",
  states: { searching: {} },
}).chart({ offers: { search: any }, states: { searching: { on: { search: [] } } } });
