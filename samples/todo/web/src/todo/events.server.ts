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
    /** The Idempotency-Key of the command whose processing published the event. */
    readonly resultOf?: string;
  };
}[EventName];

export const events = new EventPublisher<{ todo: TodoEvent }>();

/** Publishes the event that the processing of the command with the Idempotency-Key in `headers`, if any, emits. */
export function publish(event: Omit<TodoEvent, "id" | "resultOf">, headers: Headers): void {
  const resultOf = headers.get("Idempotency-Key");
  events.publish("todo", { id: crypto.randomUUID(), ...event, ...(resultOf === null ? {} : { resultOf }) });
}
