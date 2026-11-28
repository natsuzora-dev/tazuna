import { asc, gt, inArray, isNull } from "drizzle-orm";
import type { BaseSQLiteDatabase } from "drizzle-orm/sqlite-core";
import { integer, sqliteTable, text } from "drizzle-orm/sqlite-core";

/**
 * Events a service publishes, written in the same transaction as the change they report (the transactional outbox
 * pattern). The relay delivers them to other services after the commit.
 */
export const outbox = sqliteTable("outbox", {
  id: integer().primaryKey({ autoIncrement: true }),
  type: text().notNull(),
  payload: text({ mode: "json" }).notNull(),
  occurredAt: integer().notNull(),
  publishedAt: integer(),
});

export interface Message {
  id: number;
  type: string;
  payload: unknown;
}

/** A published event: its type names it, such as `order.placed`, and `data` is its payload. */
export interface DomainEvent {
  type: string;
  data: unknown;
}

type Db = BaseSQLiteDatabase<"sync", unknown, Record<string, unknown>>;

export function publish(tx: Db, event: DomainEvent, now: number): void {
  tx.insert(outbox).values({ type: event.type, payload: event.data, occurredAt: now }).run();
}

export interface OutboxReader {
  unpublished(): Message[];
  markPublished(ids: number[], now: number): void;
  /** Every message after `id`, published or not, in the order they were written. */
  after(id: number): Message[];
}

export function outboxReader(db: Db): OutboxReader {
  const select = () => db.select({ id: outbox.id, type: outbox.type, payload: outbox.payload }).from(outbox);
  return {
    unpublished: () => select().where(isNull(outbox.publishedAt)).orderBy(asc(outbox.id)).all(),
    markPublished: (ids, now) => {
      db.update(outbox).set({ publishedAt: now }).where(inArray(outbox.id, ids)).run();
    },
    after: (id) => select().where(gt(outbox.id, id)).orderBy(asc(outbox.id)).all(),
  };
}
