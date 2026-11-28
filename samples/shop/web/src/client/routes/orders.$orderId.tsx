import { useMutation, useQuery, useQueryClient } from "@tanstack/react-query";
import { createFileRoute } from "@tanstack/react-router";
import { body, money, ordersApi } from "../api.ts";

export const Route = createFileRoute("/orders/$orderId")({ component: OrderPage });

const statusLabels = {
  awaiting_stock: "Waiting for stock",
  awaiting_payment: "Waiting for payment",
  confirmed: "Confirmed",
  cancelled: "Cancelled",
} as const;

const reasonLabels = {
  customer: "you cancelled it",
  out_of_stock: "a product is out of stock",
  payment_failed: "the payment failed",
  payment_timeout: "it was not paid in time",
} as const;

function OrderPage() {
  const { orderId } = Route.useParams();
  const queryClient = useQueryClient();
  const order = useQuery({
    queryKey: ["order", orderId],
    queryFn: () => ordersApi.orders[":id"].$get({ param: { id: orderId } }).then(body),
    refetchInterval: (query) =>
      ["awaiting_stock", "awaiting_payment"].includes(query.state.data?.status ?? "") ? 1000 : false,
  });
  const cancel = useMutation({
    mutationFn: () => ordersApi.orders[":id"].cancel.$post({ param: { id: orderId } }).then((r) => r.ok),
    onSettled: () => queryClient.invalidateQueries({ queryKey: ["order", orderId] }),
  });

  if (!order.data) return <p>{order.error ? order.error.message : "Loading…"}</p>;
  const { status, cancelReason, total, lines, payBy } = order.data;
  const open = status === "awaiting_stock" || status === "awaiting_payment";

  return (
    <section>
      <h1>Order {orderId.slice(0, 8)}</h1>
      <p role="status">
        {statusLabels[status]}
        {cancelReason && `: ${reasonLabels[cancelReason]}`}
      </p>
      <ul>
        {lines.map((line, index) => (
          // biome-ignore lint/suspicious/noArrayIndexKey: an order's lines never change or move
          <li key={index}>
            {line.quantity} × {line.sku}
          </li>
        ))}
      </ul>
      <p>Total {money(total)}</p>
      {open && <p>Pay by {new Date(payBy).toLocaleTimeString("en-US", { timeZone: "UTC" })} UTC</p>}
      {open && (
        <button type="button" onClick={() => cancel.mutate()} disabled={cancel.isPending}>
          Cancel order
        </button>
      )}
    </section>
  );
}
