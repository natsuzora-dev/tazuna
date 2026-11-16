import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import type { Json } from "../data/values.ts";

/** The part of a command that two commands with the same id are compared by. `input` is canonical. */
export interface Request {
  readonly name: string;
  readonly input: unknown;
}

/** The first recorded answer for each id and the request that it answered. */
export type CommandAnswers = Map<string, { readonly request: Request; readonly answer: Answer }>;

export function answerAgain(known: { readonly request: Request; readonly answer: Answer }, request: Request): Answer {
  const same =
    known.request.name === request.name && JSON.stringify(known.request.input) === JSON.stringify(request.input);
  return same ? known.answer : { result: "rejected", rejection: { kind: "reused-id" } };
}

function keepsAnswer(answer: Answer): boolean {
  return answer.result !== "rejected" || answer.rejection.kind !== "invalid-input";
}

export function keep(table: CommandAnswers, id: string, request: Request, answer: Answer): void {
  if (keepsAnswer(answer)) table.set(id, { request, answer });
}

/** A delivered event. `payload` is canonical. */
export interface Delivery {
  readonly event: DefinitionRef;
  readonly payload: Json;
}

/** The first delivered event for each id. */
export type EventDeliveries = Map<string, Delivery>;

export function sameDelivery(a: Delivery, b: Delivery): boolean {
  return sameRef(a.event, b.event) && JSON.stringify(a.payload) === JSON.stringify(b.payload);
}

export function malformedRedelivery(
  id: string,
  first: Delivery,
  delivered: Delivery,
): Extract<InvalidInput, { readonly kind: "InvalidInput.changedRedeliveryPayload" | "InvalidInput.reusedEventId" }> {
  return sameRef(first.event, delivered.event)
    ? {
        kind: "InvalidInput.changedRedeliveryPayload",
        definition: null,
        data: { eventId: id, event: delivered.event, firstPayload: first.payload, deliveredPayload: delivered.payload },
      }
    : {
        kind: "InvalidInput.reusedEventId",
        definition: null,
        data: { eventId: id, firstEvent: first.event, deliveredEvent: delivered.event },
      };
}
