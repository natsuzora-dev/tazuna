import { contract } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const uncheckedTodo = contract({ addTask });
