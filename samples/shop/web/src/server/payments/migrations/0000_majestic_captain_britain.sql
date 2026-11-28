CREATE TABLE `outbox` (
	`id` integer PRIMARY KEY AUTOINCREMENT NOT NULL,
	`type` text NOT NULL,
	`payload` text NOT NULL,
	`occurred_at` integer NOT NULL,
	`published_at` integer
);
--> statement-breakpoint
CREATE TABLE `payments` (
	`order_id` text PRIMARY KEY NOT NULL,
	`amount_cents` integer NOT NULL,
	`status` text NOT NULL,
	`transaction_id` text,
	`order_cancelled` integer DEFAULT false NOT NULL,
	`charge_reference` text NOT NULL,
	`refund_reference` text,
	`created_at` integer NOT NULL,
	CONSTRAINT "payments_amount" CHECK("payments"."amount_cents" > 0),
	CONSTRAINT "payments_transaction" CHECK("payments"."status" not in ('captured', 'refunding', 'refund_refused') or "payments"."transaction_id" is not null)
);
--> statement-breakpoint
CREATE UNIQUE INDEX `payments_chargeReference_unique` ON `payments` (`charge_reference`);--> statement-breakpoint
CREATE UNIQUE INDEX `payments_refundReference_unique` ON `payments` (`refund_reference`);