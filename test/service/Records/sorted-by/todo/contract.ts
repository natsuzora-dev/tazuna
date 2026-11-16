import {
  checkPlan,
  contract,
  Entry,
  listTasks,
  listVisits,
  planChecked,
  planTasks,
  tasksListed,
  tasksPlanned,
  Visit,
  visitsListed,
} from "./todo.ts";

export const todo = contract({
  Entry,
  Visit,
  listTasks,
  tasksListed,
  planTasks,
  tasksPlanned,
  listVisits,
  visitsListed,
  checkPlan,
  planChecked,
});
