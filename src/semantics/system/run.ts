import type { Step } from "../../data/step.generated.ts";
import type { Processing } from "../chart/queue.ts";
import { type Pending, writeInput } from "../state.ts";
import {
  advance,
  call,
  cannotOperate,
  checkOrderUsed,
  checkUncreatedKeys,
  endSubscription,
  mock,
  operate,
  receive,
  send,
  subscribe,
} from "./input.ts";
import { restart } from "./restart.ts";

export const given = ({ id }: { readonly id?: string | undefined }) => (id === undefined ? {} : { id });

/** Processes the input in the state that `advance` makes for it. */
function arrive(r: Processing, input: Step): Pending | undefined {
  switch (input.type) {
    case "time":
      writeInput(r.state, { dir: "in", type: "time" });
      return;
    case "restart":
      restart(r);
      return;
    case "command":
      send(r, input.name, input.input, given(input));
      return;
    case "query":
      call(r, input.name, input.input, given(input));
      return;
    case "event":
      receive(r, input.name, input.payload, given(input), input.resultOf);
      return;
    case "operation":
      operate(r, input.screen, input.control, input.payload);
      return;
    case "unacceptedOperation":
      cannotOperate(r, input.screen, input.control, input.payload);
      return;
    case "answer":
      return mock(r, input);
    case "subscribe":
      subscribe(r, input.name, input.input, given(input));
      return;
    case "unsubscribe":
      endSubscription(r, input.to);
      return;
  }
}

/**
 * Processes an input, which arrives at its time after the deadlines due by then, and returns the request that a mock
 * input answered. Only TS has `arrived`, which hears the trace line count when the input arrives, and the returned
 * request.
 */
export function step(r: Processing, input: Step, arrived: (line: number) => void): Pending | undefined {
  const deadlineOrder = input.deadlineOrder ?? [];
  r.state.inputDeadlineOrder = deadlineOrder;
  r.state.deadlineOrder = deadlineOrder;
  r.state.stepOrder = input.stepOrder ?? [];
  r.state.keyNames = new Map(Object.entries(input.keys ?? {}));
  advance(r, input);
  arrived(r.state.lines.length);
  checkUncreatedKeys(r, input);
  const answered = arrive(r, input);
  checkOrderUsed(r);
  return answered;
}
