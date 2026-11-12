import { EventPublisher } from "@orpc/server";
import type { todo } from "@todo/spec/todo";
import type { z } from "zod";

type Todo = typeof todo;
type EventName = { [K in keyof Todo]: Todo[K] extends { readonly kind: "event" } ? K : never }[keyof Todo];

export type TodoEvent = {
  [K in EventName]: {
    readonly id: string;
    readonly name: K;
    readonly payload: z.output<z.ZodObject<Todo[K]["payload"]>>;
  };
}[EventName];

export const events = new EventPublisher<{ todo: TodoEvent }>();

export function publish(event: Omit<TodoEvent, "id">): void {
  events.publish("todo", { id: crypto.randomUUID(), ...event });
}
