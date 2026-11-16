import { contract, markSeen, taskAdded, tasks } from "./todo.ts";

export const todo = contract({ markSeen, taskAdded, tasks });
