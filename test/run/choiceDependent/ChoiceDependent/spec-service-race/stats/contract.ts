import { contract } from "@natsuzora-dev/tazuna";
import { countCompleted, resetCount, resumeCounting } from "./stats.ts";

export const stats = contract({ countCompleted, resetCount, resumeCounting });
