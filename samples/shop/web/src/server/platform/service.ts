import type { Hono } from "hono";
import type { z } from "zod";
import type { Env } from "./http.ts";
import type { Message, OutboxReader } from "./outbox.ts";

/** What a service shows the rest of the shop: its HTTP API, the events it consumes, its scheduled work, and its outbox. */
export interface Service<Routes extends Hono<Env> = Hono<Env>> {
  name: string;
  routes: Routes;
  /** Handles one event another service published. Types the service does not consume are ignored. */
  handle(message: Message): Promise<void>;
  subscribes: readonly string[];
  /** Runs the work that is due at the clock's time. */
  tick(): Promise<void>;
  outbox: OutboxReader;
}

type Handlers = { [type: string]: { schema: z.ZodType; handle: (data: never) => void | Promise<void> } };

/** Builds `handle` from one schema and handler per event type. Each consumer parses only the fields it reads. */
export function consumer(handlers: Handlers): Pick<Service, "handle" | "subscribes"> {
  return {
    subscribes: Object.keys(handlers),
    async handle(message) {
      const handler = handlers[message.type];
      if (!handler) return;
      const parsed = handler.schema.safeParse(message.payload);
      if (!parsed.success) {
        console.error(`dropped ${message.type} message ${message.id}`, parsed.error.issues);
        return;
      }
      await handler.handle(parsed.data as never);
    },
  };
}

export function on<S extends z.ZodType>(schema: S, handle: (data: z.infer<S>) => void | Promise<void>) {
  return { schema, handle };
}
