import { contract, Entry, listTasks, orderedTaskGroups, tagTask, taskGroups, tasksListed } from "./todo.ts";

export const todo = contract({ Entry, listTasks, tasksListed, taskGroups, orderedTaskGroups, tagTask });
