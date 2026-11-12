import { contract } from "@natsuzora-dev/tazuna";
import { addTask, reminded } from "./twoDeadlinesTodo.ts";

export const twoDeadlinesTodo = contract({ addTask, reminded });
