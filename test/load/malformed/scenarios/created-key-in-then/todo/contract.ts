import { addNote, addTask, contract, noteIds } from "./todo.ts";

export const todo = contract({ addTask, addNote, noteIds });
