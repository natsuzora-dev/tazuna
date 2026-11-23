import { addTask, addTasks, contract, markSeen, noted, ping, taskAdded, tasks } from "./todo.ts";

export const todo = contract({ addTask, addTasks, markSeen, noted, ping, taskAdded, tasks });
