import { asc, eq, inArray, sql } from "drizzle-orm";
import type { Clock } from "../platform/clock.ts";
import { openDatabase } from "../platform/db.ts";
import { publish } from "../platform/outbox.ts";
import * as schema from "./schema.ts";
import { reservationLines, reservations, stock } from "./schema.ts";

export interface Line {
  sku: string;
  quantity: number;
}

/** The events inventory publishes. */
export type InventoryEvent =
  | { type: "stock.restocked"; data: { sku: string; units: number } }
  | { type: "stock.reserved"; data: { orderId: string; lines: Line[] } }
  | { type: "stock.reservation_failed"; data: { orderId: string } };

export function openInventoryDb(file = ":memory:") {
  return openDatabase(file, schema, `${import.meta.dirname}/migrations`);
}

export type InventoryDb = ReturnType<typeof openInventoryDb>;
type Tx = Parameters<Parameters<InventoryDb["transaction"]>[0]>[0];

/** Units per SKU that the lines ask for in all. */
function unitsBySku(lines: Line[]): Map<string, number> {
  const units = new Map<string, number>();
  for (const { sku, quantity } of lines) units.set(sku, (units.get(sku) ?? 0) + quantity);
  return units;
}

export function createInventory({ db, clock }: { db: InventoryDb; clock: Clock }) {
  const emit = (tx: Tx, event: InventoryEvent) => publish(tx, event, clock.now());

  function shift(tx: Tx, lines: Line[], sign: 1 | -1) {
    for (const [sku, units] of unitsBySku(lines)) {
      tx.update(stock)
        .set({ onHand: sql`${stock.onHand} + ${sign * units}` })
        .where(eq(stock.sku, sku))
        .run();
    }
  }

  const reservedLines = (tx: Tx, orderId: string) =>
    tx
      .select({ sku: reservationLines.sku, quantity: reservationLines.quantity })
      .from(reservationLines)
      .where(eq(reservationLines.orderId, orderId))
      .orderBy(asc(reservationLines.position))
      .all();

  const isReserved = (tx: Tx, orderId: string) =>
    tx.select().from(reservations).where(eq(reservations.orderId, orderId)).get() !== undefined;

  return {
    onHand: (sku: string) => db.select().from(stock).where(eq(stock.sku, sku)).get()?.onHand ?? 0,

    restock(sku: string, units: number) {
      return db.transaction((tx) => {
        const row = tx
          .insert(stock)
          .values({ sku, onHand: units })
          .onConflictDoUpdate({ target: stock.sku, set: { onHand: sql`${stock.onHand} + ${units}` } })
          .returning()
          .get();
        emit(tx, { type: "stock.restocked", data: { sku, units } });
        return row;
      });
    },

    /**
     * Reserves every line of a placed order, or none of them when a product is short. An order is reserved once, and
     * a line for no units or fewer is ignored as a malformed order.
     */
    reserve(orderId: string, lines: Line[]) {
      db.transaction((tx) => {
        if (isReserved(tx, orderId) || lines.some((line) => line.quantity <= 0)) return;
        const wanted = unitsBySku(lines);
        const onHand = new Map(
          tx
            .select()
            .from(stock)
            .where(inArray(stock.sku, [...wanted.keys()]))
            .all()
            .map((row) => [row.sku, row.onHand]),
        );
        const available = [...wanted].every(([sku, units]) => {
          const have = onHand.get(sku);
          return have !== undefined && units <= have;
        });
        if (!available) {
          emit(tx, { type: "stock.reservation_failed", data: { orderId } });
          return;
        }
        shift(tx, lines, -1);
        tx.insert(reservations).values({ orderId, reservedAt: clock.now() }).run();
        if (lines.length > 0) {
          tx.insert(reservationLines)
            .values(lines.map((line, position) => ({ orderId, position, ...line })))
            .run();
        }
        emit(tx, { type: "stock.reserved", data: { orderId, lines } });
      });
    },

    /** Puts a cancelled order's stock back on the shelf. */
    release(orderId: string) {
      db.transaction((tx) => {
        if (!isReserved(tx, orderId)) return;
        shift(tx, reservedLines(tx, orderId), 1);
        tx.delete(reservations).where(eq(reservations.orderId, orderId)).run();
      });
    },

    /** A confirmed order's stock is sold: the reservation ends and the units stay off the shelf. */
    commit(orderId: string) {
      db.delete(reservations).where(eq(reservations.orderId, orderId)).run();
    },
  };
}

export type Inventory = ReturnType<typeof createInventory>;
