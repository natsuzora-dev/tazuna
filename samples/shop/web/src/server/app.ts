import { Hono } from "hono";
import { requestId } from "hono/request-id";
import type { Clock } from "./platform/clock.ts";
import type { Env } from "./platform/http.ts";
import { createRelay } from "./platform/relay.ts";
import type { Service } from "./platform/service.ts";
import { session, sessionRoutes } from "./platform/session.ts";

/**
 * The shop as one deployable: each service's API under `/api/<service>`, the relay that carries events between
 * services, and the tick that runs scheduled work.
 */
export function createShop({
  services,
  clock,
  sessionSecret,
}: {
  services: readonly Service[];
  clock: Clock;
  sessionSecret: string;
}) {
  const relay = createRelay(services, clock);
  const app = new Hono<Env>()
    .use("/api/*", requestId(), session(sessionSecret), async (_c, next) => {
      await next();
      relay.schedule();
    })
    .route("/api/session", sessionRoutes(sessionSecret));
  for (const service of services) app.route(`/api/${service.name}`, service.routes);

  return {
    app,
    async tick() {
      for (const service of services) await service.tick();
      relay.schedule();
    },
    /** Resolves once every published event has been delivered. */
    settled: () => relay.settled(),
  };
}

export type Shop = ReturnType<typeof createShop>;
