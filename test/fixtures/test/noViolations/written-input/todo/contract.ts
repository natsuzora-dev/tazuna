import { addItem, contract, itemAdded } from "./todo.ts";

export const todo = contract({ addItem, itemAdded });
