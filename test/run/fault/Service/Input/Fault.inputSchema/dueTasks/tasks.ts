import { datetime, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = service({ name: "dueTasks", description: "Count the tasks due by a time" });

export const dueBy = query({
  input: { by: datetime },
  output: { count: z.int() },
}).resolve(() => ({ count: 0 }));

export const dueTasks = contract({ dueBy });
