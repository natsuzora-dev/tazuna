import { useMutation, useQuery } from "@tanstack/react-query";
import { createFileRoute, useNavigate } from "@tanstack/react-router";
import { type FormEvent, useState } from "react";
import { body, inventoryApi, money, ordersApi } from "../api.ts";

export const Route = createFileRoute("/")({ component: Shop });

function Shop() {
  const navigate = useNavigate();
  const prices = useQuery({ queryKey: ["prices"], queryFn: () => ordersApi.prices.$get().then(body) });
  const [email, setEmail] = useState("");
  const [quantities, setQuantities] = useState<Record<string, number>>({});
  const place = useMutation({
    mutationFn: () => {
      const lines = Object.entries(quantities)
        .filter(([, quantity]) => quantity > 0)
        .map(([sku, quantity]) => ({ sku, quantity }));
      return ordersApi.orders.$post({ json: { email, lines } }).then(body);
    },
    onSuccess: (order) => navigate({ to: "/orders/$orderId", params: { orderId: order.id } }),
  });

  const submit = (event: FormEvent) => {
    event.preventDefault();
    place.mutate();
  };

  return (
    <form onSubmit={submit}>
      <h1>Shop</h1>
      <table>
        <thead>
          <tr>
            <th>Product</th>
            <th>Price</th>
            <th>In stock</th>
            <th>Quantity</th>
          </tr>
        </thead>
        <tbody>
          {prices.data?.map(({ sku, price }) => (
            <tr key={sku}>
              <td>{sku}</td>
              <td>{money(price)}</td>
              <td>
                <InStock sku={sku} />
              </td>
              <td>
                <input
                  type="number"
                  min={0}
                  max={10}
                  aria-label={`Quantity of ${sku}`}
                  value={quantities[sku] ?? 0}
                  onChange={(event) => setQuantities({ ...quantities, [sku]: Number(event.target.value) })}
                />
              </td>
            </tr>
          ))}
        </tbody>
      </table>
      <label>
        Email <input type="email" value={email} onChange={(event) => setEmail(event.target.value)} />
      </label>
      <button type="submit" disabled={place.isPending}>
        Place order
      </button>
      {place.error && <p role="alert">{place.error.message}</p>}
    </form>
  );
}

function InStock({ sku }: { sku: string }) {
  const stock = useQuery({
    queryKey: ["stock", sku],
    queryFn: () => inventoryApi.stock.$get({ query: { sku } }).then(body),
    retry: false,
  });
  return <span>{stock.data?.onHand ?? "?"}</span>;
}
