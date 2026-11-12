import { createORPCErrorFromJson } from "@orpc/client";
import { ORPCError, os } from "@orpc/server";
import { eq } from "drizzle-orm";
import { db } from "../db/index.server.ts";
import { commandAnswers, type StoredAnswer } from "../db/schema.ts";
import { commandErrors } from "./errors.ts";

async function answerOf(run: () => Promise<unknown>): Promise<StoredAnswer> {
  try {
    return { output: await run() };
  } catch (error) {
    if (error instanceof ORPCError) return { error: error.toJSON() };
    throw error;
  }
}

const answering = new Map<string, { readonly request: string; readonly answer: Promise<StoredAnswer> }>();

const earlierAnswer = (key: string) =>
  answering.get(key) ?? db.select().from(commandAnswers).where(eq(commandAnswers.key, key)).get();

async function answerOnce(key: string, request: string, run: () => Promise<unknown>): Promise<StoredAnswer> {
  const answer = answerOf(run);
  answering.set(key, { request, answer });
  try {
    const answered = await answer;
    db.insert(commandAnswers).values({ key, request, answer: answered }).run();
    return answered;
  } finally {
    answering.delete(key);
  }
}

const base = os
  .$context<{ headers: Headers }>()
  .errors({ IDEMPOTENCY_KEY_REUSED: commandErrors.IDEMPOTENCY_KEY_REUSED });

const idempotency = base.middleware(async ({ context, path, next, errors }, input, output) => {
  const key = context.headers.get("Idempotency-Key");
  if (key === null) return next();
  const request = JSON.stringify({ path, input });
  const earlier = earlierAnswer(key);
  if (earlier !== undefined && earlier.request !== request) throw errors.IDEMPOTENCY_KEY_REUSED();
  const answer = await (earlier?.answer ?? answerOnce(key, request, async () => (await next()).output));
  if ("error" in answer) throw createORPCErrorFromJson(answer.error);
  return output(answer.output);
});

export const command = base.$config({ initialInputValidationIndex: Number.NEGATIVE_INFINITY }).use(idempotency);
