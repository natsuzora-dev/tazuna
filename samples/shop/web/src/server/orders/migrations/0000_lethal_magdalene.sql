CREATE TABLE `order_lines` (
	`order_id` text NOT NULL,
	`position` integer NOT NULL,
	`sku` text NOT NULL,
	`quantity` integer NOT NULL,
	PRIMARY KEY(`order_id`, `position`),
	FOREIGN KEY (`order_id`) REFERENCES `orders`(`id`) ON UPDATE no action ON DELETE no action
);
--> statement-breakpoint
CREATE TABLE `orders` (
	`id` text PRIMARY KEY NOT NULL,
	`email` text NOT NULL,
	`total_cents` integer NOT NULL,
	`status` text NOT NULL,
	`cancel_reason` text,
	`placed_at` integer NOT NULL,
	`pay_by` integer NOT NULL,
	CONSTRAINT "orders_cancel_reason" CHECK(("orders"."status" = 'cancelled') = ("orders"."cancel_reason" is not null))
);
--> statement-breakpoint
CREATE INDEX `orders_status_pay_by` ON `orders` (`status`,`pay_by`);--> statement-breakpoint
CREATE TABLE `outbox` (
	`id` integer PRIMARY KEY AUTOINCREMENT NOT NULL,
	`type` text NOT NULL,
	`payload` text NOT NULL,
	`occurred_at` integer NOT NULL,
	`published_at` integer
);
--> statement-breakpoint
CREATE TABLE `prices` (
	`sku` text PRIMARY KEY NOT NULL,
	`price_cents` integer NOT NULL
);
