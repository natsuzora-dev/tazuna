import { addTask, contract, markSeen, noted, ping, taskAdded, tasks } from "./todo.ts";

export const todo = contract({ addTask, markSeen, noted, ping, taskAdded, tasks });
