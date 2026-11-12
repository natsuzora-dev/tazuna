import type { InferRouterOutputs, InferSchemaOutput, Schema } from "@orpc/server";
import type * as Notifier from "../../src/notifier/notifier.server.ts";
import type { todoRouter } from "../../src/todo/todo.router.ts";

type TodoRouter = typeof todoRouter;

type Procedures = {
  readonly [K in keyof TodoRouter]: (
    input: TodoRouter[K]["~orpc"] extends { inputSchema?: infer S extends Schema<unknown, unknown> }
      ? InferSchemaOutput<S>
      : never,
  ) => Promise<InferRouterOutputs<TodoRouter[K]>>;
};

type Held = Procedures & typeof Notifier;

export type HeldName = keyof Held;

export interface HeldCall<K extends HeldName> {
  readonly name: K;
  readonly input: Parameters<Held[K]>[0];
  readonly request: K extends keyof Procedures ? Request : undefined;
  readonly answer: (value: Awaited<ReturnType<Held[K]>>) => void;
  readonly fail: (error: Error) => void;
}

export type HeldCalls = { readonly [K in HeldName]?: (call: HeldCall<K>) => void };

let receivers: HeldCalls = {};

export function whenHeld(calls: HeldCalls): void {
  receivers = calls;
}

export function hold<K extends HeldName>(
  name: K,
  input: HeldCall<K>["input"],
  request: HeldCall<K>["request"],
): Promise<Awaited<ReturnType<Held[K]>>> {
  const receive = receivers[name];
  if (receive === undefined) throw new Error(`no test receives the held call ${name}`);
  return new Promise((answer, fail) => receive({ name, input, request, answer, fail }));
}
