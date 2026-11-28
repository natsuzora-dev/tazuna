// How each service's boundary reads in the spec's terms: which route is which command or query, which published
// event is which spec event, and which gateway webhook is which answer. The app never sees these names.

import type { WebhookEvent } from "../src/server/payments/index.ts";

// biome-ignore lint/suspicious/noExplicitAny: trace values are untyped JSON
type Json = any;

export interface RequestOp {
  /** The spec's command or query. */
  name: string;
  /** The app's route under `/api/<service>`. A command with none runs only inside the service (`tazuna.Own`). */
  route?: { method: "GET" | "POST"; path: string };
  /** The spec's input, read off an HTTP request. */
  input?(request: { params: Record<string, string>; query: URLSearchParams; body: Json }): Json;
  /** The HTTP request for a spec input. */
  request?(input: Json): { params?: Record<string, string>; query?: Record<string, string>; body?: Json };
  /** A query's answer, read off its response. */
  output?(status: number, body: Json): Json;
  /** The spec's rule for each validation error path. */
  rules?: [RegExp, string][];
  /** The spec's rejection for each problem type. */
  rejections?: Record<string, string>;
}

export interface Inbound {
  /** The app's event type, and the spec's source, publisher, value tag, and the tag that wraps it on arrival. */
  type: string;
  source: string;
  publisher: string;
  tag: string;
  wrap: string;
  toSpec(data: Json): Json;
  fromSpec(value: Json): Json;
}

export interface ServiceMapping {
  requests: RequestOp[];
  /** The spec event for each event the service publishes. */
  events: Record<string, (data: Json) => Json>;
  inbound: Inbound[];
  /** Ids an out line makes, beside request ids. */
  makes(value: Json): string[];
}

const line = ({ sku, quantity }: Json) => ({ tag: "Line", sku, quantity });
const tag = (name: Json) => ({ tag: name });
const some = (value: Json) => ({ tag: "Some", 0: value });
const none = { tag: "None" };

function aboutOrder(type: string, source: string, publisher: string, specTag: string, wrap: string): Inbound {
  return {
    type,
    source,
    publisher,
    tag: specTag,
    wrap,
    toSpec: (data) => ({ tag: specTag, order: data.orderId }),
    fromSpec: (value) => ({ orderId: value.order }),
  };
}

const ordersInbound = (wrap: string): Inbound[] => [
  {
    type: "order.placed",
    source: "order",
    publisher: "orders",
    tag: "OrderPlaced",
    wrap,
    toSpec: (data) => ({ tag: "OrderPlaced", order: data.orderId, lines: data.lines.map(line) }),
    fromSpec: (value) => ({
      orderId: value.order,
      lines: value.lines.map(({ sku, quantity }: Json) => ({ sku, quantity })),
    }),
  },
  {
    type: "order.payment_requested",
    source: "order",
    publisher: "orders",
    tag: "PaymentDue",
    wrap,
    toSpec: (data) => ({ tag: "PaymentDue", order: data.orderId, amount: data.amount }),
    fromSpec: (value) => ({ orderId: value.order, amount: value.amount }),
  },
  aboutOrder("order.confirmed", "order", "orders", "OrderConfirmed", wrap),
  aboutOrder("order.cancelled", "order", "orders", "OrderCancelled", wrap),
];

const cancelReasons: Record<string, string> = {
  customer: "ByCustomer",
  out_of_stock: "OutOfStock",
  payment_failed: "PaymentFailed",
  payment_timeout: "NotPaidInTime",
};

const orderStatuses: Record<string, string> = {
  awaiting_stock: "AwaitingStock",
  awaiting_payment: "AwaitingPayment",
  confirmed: "Confirmed",
};

const orderStatus = ({ status, cancelReason }: Json) =>
  status === "cancelled" ? { tag: "Cancelled", reason: tag(cancelReasons[cancelReason]) } : tag(orderStatuses[status]);

const paymentStatus = ({ status, transactionId: transaction }: Json) =>
  ({
    charging: tag("Charging"),
    captured: { tag: "Captured", transaction },
    declined: tag("Declined"),
    refunding: { tag: "Refunding", transaction },
    refunded: tag("Refunded"),
    refund_refused: { tag: "RefundRefused", transaction },
  })[status as string];

/** A request whose input is the id in its path. */
const byId = (method: "GET" | "POST", path: string) => ({
  route: { method, path },
  input: ({ params }: { params: Record<string, string> }) => params.id,
  request: (id: string) => ({ params: { id } }),
});

export const mappings: Record<string, ServiceMapping> = {
  orders: {
    requests: [
      {
        name: "set price",
        route: { method: "POST", path: "/prices" },
        input: ({ body }) => ({ tag: "NewPrice", sku: body.sku, price: body.price }),
        request: ({ sku, price }) => ({ body: { sku, price } }),
        rules: [
          [/^sku$/, "sku is given"],
          [/^price$/, "price is positive"],
        ],
      },
      {
        name: "place order",
        route: { method: "POST", path: "/orders" },
        input: ({ body }) => ({ tag: "NewOrder", email: body.email, lines: body.lines.map(line) }),
        request: ({ email, lines }) => ({
          body: { email, lines: lines.map(({ sku, quantity }: Json) => ({ sku, quantity })) },
        }),
        rules: [
          [/^email$/, "email is given"],
          [/^lines$/, "an order has a line"],
          [/^lines\.\d+\.quantity$/, "each quantity is 1 to 10"],
        ],
        rejections: { checkout_limit_reached: "TooManyCheckouts", unknown_product: "UnknownProduct" },
      },
      {
        name: "cancel order",
        ...byId("POST", "/orders/:id/cancel"),
        rejections: { order_not_found: "NoSuchOrder", order_not_open: "NotOpen" },
      },
      {
        name: "order status",
        ...byId("GET", "/orders/:id"),
        output: (status, body) => (status === 404 ? none : some(orderStatus(body))),
      },
      { name: "request payment" },
      { name: "confirm" },
      { name: "cancel for" },
    ],
    events: {
      "price.set": ({ sku, price }) => ({ tag: "PriceSet", sku, price }),
      "order.placed": ({ orderId, email, lines, total }) => ({
        tag: "Placed",
        order: orderId,
        email,
        lines: lines.map(line),
        total,
      }),
      "order.payment_requested": ({ orderId, amount }) => ({ tag: "PaymentDue", order: orderId, amount }),
      "order.confirmed": ({ orderId }) => ({ tag: "OrderConfirmed", order: orderId }),
      "order.cancelled": ({ orderId, reason }) => ({
        tag: "OrderCancelled",
        order: orderId,
        reason: tag(cancelReasons[reason]),
      }),
    },
    inbound: [
      aboutOrder("stock.reserved", "stock", "inventory", "StockHeld", "StockNews"),
      aboutOrder("stock.reservation_failed", "stock", "inventory", "OutOfStock", "StockNews"),
      aboutOrder("payment.captured", "payment", "payments", "PaymentCaptured", "PaymentNews"),
      aboutOrder("payment.declined", "payment", "payments", "PaymentFailed", "PaymentNews"),
    ],
    makes: (value) => (value.tag === "Placed" ? [value.order] : []),
  },

  inventory: {
    requests: [
      {
        name: "restock",
        route: { method: "POST", path: "/deliveries" },
        input: ({ body }) => ({ tag: "Delivery", sku: body.sku, units: body.units }),
        request: ({ sku, units }) => ({ body: { sku, units } }),
        rules: [
          [/^sku$/, "sku is given"],
          [/^units$/, "units is positive"],
        ],
      },
      {
        name: "stock level",
        route: { method: "GET", path: "/stock" },
        input: ({ query }) => query.get("sku") ?? "",
        request: (sku) => ({ query: { sku } }),
        output: (_status, body) => body.onHand,
      },
      { name: "hold" },
    ],
    events: {
      "stock.restocked": ({ sku, units }) => ({ tag: "Restocked", sku, units }),
      "stock.reserved": ({ orderId, lines }) => ({ tag: "Held", order: orderId, lines: lines.map(line) }),
      "stock.reservation_failed": ({ orderId }) => ({ tag: "Unavailable", order: orderId }),
    },
    inbound: ordersInbound("OrderNews"),
    makes: () => [],
  },

  payments: {
    requests: [
      {
        name: "payment status",
        ...byId("GET", "/payments/:id"),
        output: (status, body) => (status === 404 ? none : some(paymentStatus(body))),
      },
      { name: "take" },
      { name: "give back" },
    ],
    events: {
      "payment.charge_started": ({ orderId, amount }) => ({ tag: "ChargeStarted", order: orderId, amount }),
      "payment.captured": ({ orderId, transaction }) => ({ tag: "ChargeCaptured", order: orderId, transaction }),
      "payment.declined": ({ orderId }) => ({ tag: "ChargeDeclined", order: orderId }),
      "payment.refund_started": ({ orderId, transaction }) => ({ tag: "RefundStarted", order: orderId, transaction }),
      "payment.refunded": ({ orderId }) => ({ tag: "RefundDone", order: orderId }),
      "payment.refund_failed": ({ orderId }) => ({ tag: "RefundFailed", order: orderId }),
    },
    inbound: ordersInbound("OrderNews"),
    makes: () => [],
  },
};

/** The gateway's webhook route, which carries the answers to the shop's charge and refund requests. */
export const webhookRoute = { service: "payments", method: "POST", path: "/webhooks/paygate" } as const;

const failures: Record<string, string> = {
  card_declined: "CardDeclined",
  insufficient_funds: "InsufficientFunds",
  refund_window_closed: "RefundWindowClosed",
};

/** A gateway webhook as the spec's answer to the request it names. */
export function gatewayAnswer(event: WebhookEvent): Json {
  const to = event.reference;
  switch (event.type) {
    case "charge.succeeded":
      return { in: "answer", to, ok: { tag: "Receipt", transaction: event.transaction } };
    case "refund.succeeded":
      return { in: "answer", to, ok: null };
    case "charge.failed":
    case "refund.failed":
      return { in: "answer", to, error: tag(failures[event.failureCode]) };
  }
}

/** The webhook the gateway sends for a spec answer to a `charge` or `refund` request. */
export function gatewayWebhook(request: "charge" | "refund", answer: Json, reference: string): WebhookEvent {
  const failure = (tagName: string) => Object.keys(failures).find((code) => failures[code] === tagName) as never;
  if (request === "charge") {
    return "ok" in answer
      ? { type: "charge.succeeded", reference, transaction: answer.ok.transaction }
      : { type: "charge.failed", reference, failureCode: failure(answer.error.tag) };
  }
  return "ok" in answer
    ? { type: "refund.succeeded", reference }
    : { type: "refund.failed", reference, failureCode: failure(answer.error.tag) };
}
