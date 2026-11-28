// Records one service's trace: each input at its boundary as an `in` line, and what the service does about it (its
// HTTP answer, the events it publishes, the requests it sends out) as that input's `out` lines.

import { Hono } from "hono";
import type { Mailer } from "../src/server/orders/index.ts";
import type { PaymentGateway, WebhookEvent } from "../src/server/payments/index.ts";
import type { Clock } from "../src/server/platform/clock.ts";
import type { Env } from "../src/server/platform/http.ts";
import type { Message } from "../src/server/platform/outbox.ts";
import type { Service } from "../src/server/platform/service.ts";
import { gatewayAnswer, mappings, type RequestOp, type ServiceMapping, webhookRoute } from "./mapping.ts";

export type Line = Record<string, unknown>;

const callers = { customer: "Customer", staff: "Staff" } as const;

export class Recorder {
  readonly lines: Line[];
  readonly mapping: ServiceMapping;
  readonly #clock: Clock;
  readonly #origin: number;
  #queue: Promise<unknown> = Promise.resolve();

  constructor(service: string, clock: Clock) {
    this.lines = [{ service, trace: 1 }];
    const mapping = mappings[service];
    if (!mapping) throw new Error(`no mapping for service ${service}`);
    this.mapping = mapping;
    this.#clock = clock;
    this.#origin = clock.now();
  }

  /** Writes a line at the service's time. A trace starts at time 0, and no outcome depends on where time starts. */
  write(line: Line): void {
    this.lines.push({ ...line, time: this.#clock.now() - this.#origin });
  }

  /**
   * Runs one input to the end before the next starts, so its out lines follow its in line. The service itself takes
   * inputs concurrently; the trace format needs each one's effects together.
   */
  input<T>(work: () => Promise<T>): Promise<T> {
    const run = this.#queue.then(work);
    this.#queue = run.catch(() => {});
    return run;
  }
}

/** The spec's answer to a request, read off the HTTP response. */
function specAnswer(
  op: RequestOp,
  status: number,
  body: { type?: string; errors?: { path: string }[] } | undefined,
): Line {
  if (status === 401 || status === 403) return { outcome: "invalid", rules: ["callers"] };
  if (status === 400 && body?.type === "validation_failed") {
    const paths = (body.errors ?? []).map((error) => error.path);
    const rules = (op.rules ?? [])
      .filter(([pattern]) => paths.some((path) => pattern.test(path)))
      .map(([, rule]) => rule);
    return { outcome: "invalid", rules };
  }
  if (op.output) return { outcome: "answered", output: op.output(status, body) };
  if (status < 300) return { outcome: "accepted" };
  const rejection = body?.type && op.rejections?.[body.type];
  if (rejection) return { outcome: "rejected", rejection: { tag: rejection } };
  throw new Error(`${op.name}: no spec answer for ${status} ${JSON.stringify(body)}`);
}

/** The service with each boundary recorded. */
export function recordService(service: Service, recorder: Recorder): Service {
  const { mapping } = recorder;
  const prefix = `/api/${service.name}`;
  let seen = service.outbox.after(0).at(-1)?.id ?? 0;

  function published() {
    for (const message of service.outbox.after(seen)) {
      seen = message.id;
      const event = mapping.events[message.type];
      if (!event) throw new Error(`${service.name} published ${message.type}, which the mapping does not know`);
      recorder.write({ out: "event", value: event(message.payload) });
    }
  }

  const routes = mapping.requests.flatMap((op) =>
    op.route ? [{ op, method: op.route.method, pattern: new URLPattern({ pathname: prefix + op.route.path }) }] : [],
  );
  const webhook = service.name === webhookRoute.service ? prefix + webhookRoute.path : undefined;

  const recorded = new Hono<Env>()
    .use(async (c, next) => {
      if (c.req.method === webhookRoute.method && c.req.path === webhook) {
        return recorder.input(async () => {
          recorder.write(gatewayAnswer(JSON.parse(await c.req.text()) as WebhookEvent));
          await next();
          published();
        });
      }
      const route = routes.find(
        ({ method, pattern }) => method === c.req.method && pattern.test({ pathname: c.req.path }),
      );
      const role = c.var.role;
      if (!route || !role) return next();
      await recorder.input(async () => {
        const params = route.pattern.exec({ pathname: c.req.path })?.pathname.groups ?? {};
        const text = c.req.method === "GET" ? "" : await c.req.text();
        const input = route.op.input?.({
          params: params as Record<string, string>,
          query: new URL(c.req.url).searchParams,
          body: text ? JSON.parse(text) : undefined,
        });
        const to = c.var.requestId;
        recorder.write({ in: "request", id: to, name: route.op.name, caller: { tag: callers[role] }, input });
        await next();
        const body = await c.res.clone().text();
        recorder.write({
          out: "answer",
          to,
          ...specAnswer(route.op, c.res.status, body ? JSON.parse(body) : undefined),
        });
        published();
      });
    })
    .route("/", service.routes);

  return {
    ...service,
    routes: recorded,
    async handle(message: Message) {
      const inbound = mapping.inbound.find((entry) => entry.type === message.type);
      if (!inbound || !service.subscribes.includes(message.type)) return service.handle(message);
      await recorder.input(async () => {
        const value = inbound.toSpec(message.payload);
        recorder.write({ in: "event", name: inbound.source, source: inbound.publisher, value });
        recorder.write({ out: "event", value: { tag: inbound.wrap, news: value } });
        await service.handle(message);
        published();
      });
    },
    tick: () =>
      recorder.input(async () => {
        recorder.write({ in: "clock" });
        await service.tick();
        published();
      }),
  };
}

/** The mailer, with each mail recorded as a request to the spec's external `mailer`. */
export function recordMailer(mailer: Mailer, recorder: Recorder): Mailer {
  let sent = 0;
  return {
    send(mail) {
      recorder.write({
        out: "request",
        external: "mailer",
        name: "send",
        id: `mail-${++sent}`,
        input: { tag: "Mail", to: mail.to, subject: mail.subject },
      });
      return mailer.send(mail);
    },
  };
}

/** The gateway, with each charge and refund recorded as a request to the spec's external `payment gateway`. */
export function recordGateway(gateway: PaymentGateway, recorder: Recorder): PaymentGateway {
  const out = (name: string, id: string, input: Line) =>
    recorder.write({ out: "request", external: "payment gateway", name, id, input });
  return {
    createCharge(request) {
      out("charge", request.reference, { tag: "Charge", order: request.orderId, amount: request.amount });
      return gateway.createCharge(request);
    },
    createRefund(request) {
      out("refund", request.reference, { tag: "Refund", transaction: request.transaction, amount: request.amount });
      return gateway.createRefund(request);
    },
  };
}
