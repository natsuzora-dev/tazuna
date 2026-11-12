import { contract } from "@natsuzora-dev/tazuna";
import { addTasks, completeTask, greeted, reminded } from "./greeter.ts";

export const greeter = contract({ addTasks, completeTask, greeted, reminded });
