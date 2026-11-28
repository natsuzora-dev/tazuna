import { zValidator } from "@hono/zod-validator";
import type { Context, ValidationTargets } from "hono";
import type { ContentfulStatusCode } from "hono/utils/http-status";
import type { z } from "zod";
import type { Role } from "./session.ts";

export type Env = { Variables: { role: Role | undefined; requestId: string } };

/** An error response in the RFC 9457 problem details format. `type` is the code clients branch on. */
export function problem<S extends ContentfulStatusCode, T extends string>(
  c: Context,
  status: S,
  type: T,
  title: string,
) {
  return c.json({ type, title, status }, status, { "content-type": "application/problem+json" });
}

/** Validates one part of the request, and answers 400 with every issue found when it does not parse. */
export function validate<T extends keyof ValidationTargets, S extends z.ZodType>(target: T, schema: S) {
  return zValidator(target, schema, (result, c) => {
    if (!result.success) {
      const errors = result.error.issues.map((issue) => ({ path: issue.path.join("."), message: issue.message }));
      return c.json({ type: "validation_failed", title: "The request is not valid", status: 400, errors }, 400, {
        "content-type": "application/problem+json",
      });
    }
  });
}
