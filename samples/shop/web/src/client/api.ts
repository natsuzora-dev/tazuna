import { type ClientResponse, hc, parseResponse } from "hono/client";
import type { InventoryApi } from "../server/inventory/index.ts";
import type { OrdersApi } from "../server/orders/index.ts";
import type { PaymentsApi } from "../server/payments/index.ts";
import type { SessionApi } from "../server/platform/session.ts";

export const sessionApi = hc<SessionApi>("/api/session");
export const ordersApi = hc<OrdersApi>("/api/orders");
export const inventoryApi = hc<InventoryApi>("/api/inventory");
export const paymentsApi = hc<PaymentsApi>("/api/payments");

interface Problem {
  type: string;
  title: string;
  errors?: { path: string; message: string }[];
}

/** An error answer from the API, with the messages to show. */
export class ApiError extends Error {
  readonly problem: Problem;

  constructor(problem: Problem) {
    super(problem.errors?.map((error) => error.message).join(". ") || problem.title);
    this.problem = problem;
  }
}

/** The body of a successful answer; throws ApiError for an error answer. */
export async function body<T extends ClientResponse<unknown>>(response: T) {
  if (!response.ok) throw new ApiError((await response.json()) as Problem);
  return parseResponse(response);
}

export const money = (cents: number) =>
  new Intl.NumberFormat("en-US", { style: "currency", currency: "USD" }).format(cents / 100);
