import { createORPCClient, ORPCError } from "@orpc/client";
import { RPCLink } from "@orpc/client/fetch";
import { ClientRetryPlugin, type ClientRetryPluginContext, SimpleCsrfProtectionLinkPlugin } from "@orpc/client/plugins";
import type { RouterClient } from "@orpc/server";
import {
  createTanstackQueryUtils,
  TANSTACK_QUERY_OPERATION_CONTEXT_SYMBOL,
  type TanstackQueryOperationContext,
} from "@orpc/tanstack-query";
import type { router } from "./router.ts";
import { customJsonSerializers } from "./serializers.ts";

interface ClientContext extends ClientRetryPluginContext, TanstackQueryOperationContext {
  readonly idempotencyKey?: string;
}

const operationOf = (context: ClientContext) => context[TANSTACK_QUERY_OPERATION_CONTEXT_SYMBOL]?.type;

const link = new RPCLink<ClientContext>({
  url: () => `${window.location.origin}/api/rpc`,
  method: ({ context }) => (operationOf(context) === "live" ? "GET" : "POST"),
  headers: ({ context }) => (context.idempotencyKey === undefined ? {} : { "Idempotency-Key": context.idempotencyKey }),
  interceptors: [
    ({ next, ...options }) =>
      operationOf(options.context) === "mutation"
        ? next({ ...options, context: { ...options.context, idempotencyKey: crypto.randomUUID() } })
        : next(),
  ],
  customJsonSerializers,
  plugins: [
    new ClientRetryPlugin({
      default: {
        retry: ({ context }) => (operationOf(context) === "mutation" ? 3 : 0),
        shouldRetry: ({ error }) => !(error instanceof ORPCError),
      },
    }),
    new SimpleCsrfProtectionLinkPlugin(),
  ],
});

export const client: RouterClient<typeof router, ClientContext> = createORPCClient(link);

export const orpc = createTanstackQueryUtils(client);
