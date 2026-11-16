import { addTasks, completeTask, contract, greeted, reminded } from "./greeter.ts";

export const greeter = contract({ addTasks, completeTask, greeted, reminded });
