import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { contract, machine } = service({ name: "listener", description: "Hear the notes of todo" });

export const hearing = machine({
  description: "Hear each note",
  receives: { noted: todo.noted },
  initial: "hearing",
  states: { hearing: {} },
}).chart({
  states: { hearing: { on: { noted: [{ target: "hearing", reenter: true }] } } },
});
