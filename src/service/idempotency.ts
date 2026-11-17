import type { Answer } from "../data/trace.generated.ts";

/** The part of a command that two commands with the same id are compared by. `input` is as the client wrote it. */
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
