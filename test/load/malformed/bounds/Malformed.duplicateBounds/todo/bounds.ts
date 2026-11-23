import { bounds } from "./todo.ts";

export const fewTasks = bounds({ creates: { Task: 2 } });

export const manyTasks = bounds({ creates: { Task: 5 } });
