import { contract } from "@natsuzora-dev/tazuna";
import { count, prepare, start } from "./stock.ts";

export const stock = contract({ start, prepare, count });
