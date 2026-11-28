import { Hono } from "hono";
import { deleteCookie, getSignedCookie, setSignedCookie } from "hono/cookie";
import { createMiddleware } from "hono/factory";
import { z } from "zod";
import type { Env } from "./http.ts";
import { problem, validate } from "./http.ts";

/**
 * Who is signed in. The sample signs anyone in as a customer or as staff on request; a real shop would put its
 * identity provider here and keep the rest unchanged.
 */
export const roles = ["customer", "staff"] as const;
export type Role = (typeof roles)[number];

const cookie = "role";

export function session(secret: string) {
  return createMiddleware<Env>(async (c, next) => {
    const value = await getSignedCookie(c, secret, cookie);
    c.set(
      "role",
      roles.find((role) => role === value),
    );
    await next();
  });
}

export function sessionRoutes(secret: string) {
  return new Hono<Env>()
    .get("/", (c) => c.json({ role: c.var.role ?? null }))
    .put("/", validate("json", z.object({ role: z.enum(roles) })), async (c) => {
      const { role } = c.req.valid("json");
      await setSignedCookie(c, cookie, role, secret, { httpOnly: true, sameSite: "Lax", path: "/" });
      return c.json({ role });
    })
    .delete("/", (c) => {
      deleteCookie(c, cookie, { path: "/" });
      return c.body(null, 204);
    });
}

/** Lets the request through only for the given roles. */
export function requireRole(...allowed: Role[]) {
  return createMiddleware<Env>(async (c, next) => {
    const role = c.var.role;
    if (!role) return problem(c, 401, "unauthenticated", "Sign in first");
    if (!allowed.includes(role)) return problem(c, 403, "forbidden", "Your role cannot do this");
    await next();
  });
}

export type SessionApi = ReturnType<typeof sessionRoutes>;
