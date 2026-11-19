import type { Answer, LineId } from "../data/trace.generated.ts";
import { canonicalJson } from "../data/values.ts";
import { idKey } from "./message.ts";

/** The part of a command that two commands with the same id are compared by. `input` is as the client wrote it. */
export interface Request {
  readonly name: string;
  readonly input: unknown;
}

/** The first recorded answer for each id, by idKey, and the request that it answered. */
export type CommandAnswers = Map<string, { readonly request: Request; readonly answer: Answer }>;

/** Lean's answerAgain: the request is the same when its name and input are, whatever the order of object fields. */
export function answerAgain(known: { readonly request: Request; readonly answer: Answer }, request: Request): Answer {
  const same =
    known.request.name === request.name && canonicalJson(known.request.input) === canonicalJson(request.input);
  return same ? known.answer : { result: "rejected", rejection: { kind: "reused-id" } };
}

function keepsAnswer(answer: Answer): boolean {
  return answer.result !== "rejected" || answer.rejection.kind !== "invalid-input";
}

export function keep(table: CommandAnswers, id: LineId, request: Request, answer: Answer): void {
  if (keepsAnswer(answer)) table.set(idKey(id), { request, answer });
}
