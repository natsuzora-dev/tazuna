import { contract } from "@natsuzora-dev/tazuna";
import { addTask, reminded } from "./planner.ts";

export const planner = contract({ addTask, reminded });
