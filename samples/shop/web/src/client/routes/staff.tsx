import { useMutation, useQueryClient } from "@tanstack/react-query";
import { createFileRoute } from "@tanstack/react-router";
import { type FormEvent, useState } from "react";
import { body, inventoryApi, money, ordersApi, paymentsApi } from "../api.ts";

export const Route = createFileRoute("/staff")({ component: Staff });

function Staff() {
  return (
    <>
      <h1>Staff</h1>
      <SetPrice />
      <Restock />
      <PaymentLookup />
    </>
  );
}

function SetPrice() {
  const queryClient = useQueryClient();
  const [sku, setSku] = useState("");
  const [price, setPrice] = useState("");
  const save = useMutation({
    mutationFn: () => ordersApi.prices.$post({ json: { sku, price: Math.round(Number(price) * 100) } }).then(body),
    onSuccess: () => queryClient.invalidateQueries({ queryKey: ["prices"] }),
  });
  const submit = (event: FormEvent) => {
    event.preventDefault();
    save.mutate();
  };
  return (
    <form onSubmit={submit} aria-label="Set price">
      <h2>Set a price</h2>
      <label>
        SKU <input value={sku} onChange={(event) => setSku(event.target.value)} />
      </label>
      <label>
        Price <input inputMode="decimal" value={price} onChange={(event) => setPrice(event.target.value)} />
      </label>
      <button type="submit">Save price</button>
      {save.data && <p role="status">{`${save.data.sku} costs ${money(save.data.price)}`}</p>}
      {save.error && <p role="alert">{save.error.message}</p>}
    </form>
  );
}

function Restock() {
  const queryClient = useQueryClient();
  const [sku, setSku] = useState("");
  const [units, setUnits] = useState("");
  const receive = useMutation({
    mutationFn: () => inventoryApi.deliveries.$post({ json: { sku, units: Number(units) } }).then(body),
    onSuccess: () => queryClient.invalidateQueries({ queryKey: ["stock"] }),
  });
  const submit = (event: FormEvent) => {
    event.preventDefault();
    receive.mutate();
  };
  return (
    <form onSubmit={submit} aria-label="Receive a delivery">
      <h2>Receive a delivery</h2>
      <label>
        SKU <input value={sku} onChange={(event) => setSku(event.target.value)} />
      </label>
      <label>
        Units <input inputMode="numeric" value={units} onChange={(event) => setUnits(event.target.value)} />
      </label>
      <button type="submit">Add to stock</button>
      {receive.data && <p role="status">{`${receive.data.onHand} ${receive.data.sku} on hand`}</p>}
      {receive.error && <p role="alert">{receive.error.message}</p>}
    </form>
  );
}

const paymentLabels = {
  charging: "Charging",
  captured: "Captured",
  declined: "Declined",
  refunding: "Refunding",
  refunded: "Refunded",
  refund_refused: "Refund refused: refund by hand",
} as const;

function PaymentLookup() {
  const [orderId, setOrderId] = useState("");
  const lookup = useMutation({
    mutationFn: () => paymentsApi.payments[":orderId"].$get({ param: { orderId } }).then(body),
  });
  const submit = (event: FormEvent) => {
    event.preventDefault();
    lookup.mutate();
  };
  return (
    <form onSubmit={submit} aria-label="Find a payment">
      <h2>Find a payment</h2>
      <label>
        Order <input value={orderId} onChange={(event) => setOrderId(event.target.value)} />
      </label>
      <button type="submit">Find</button>
      {lookup.data && <p role="status">{`${money(lookup.data.amount)}: ${paymentLabels[lookup.data.status]}`}</p>}
      {lookup.error && <p role="alert">{lookup.error.message}</p>}
    </form>
  );
}
