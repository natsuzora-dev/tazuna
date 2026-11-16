import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine } = service({ description: "Watch the tags" });

export const tagWatcher = machine({
  description: "Watch each tag, one of which is empty",
  initial: "watching",
  states: { watching: { type: "map", key: { tag: z.string().min(1) }, initial: "idle", states: { idle: {} } } },
}).chart({ states: { watching: { items: () => [{ tag: "home" }, { tag: "" }] } } });
