CREATE TABLE `outbox` (
	`id` integer PRIMARY KEY AUTOINCREMENT NOT NULL,
	`type` text NOT NULL,
	`payload` text NOT NULL,
	`occurred_at` integer NOT NULL,
	`published_at` integer
);
--> statement-breakpoint
CREATE TABLE `reservation_lines` (
	`order_id` text NOT NULL,
	`position` integer NOT NULL,
	`sku` text NOT NULL,
	`quantity` integer NOT NULL,
	PRIMARY KEY(`order_id`, `position`),
	FOREIGN KEY (`order_id`) REFERENCES `reservations`(`order_id`) ON UPDATE no action ON DELETE cascade,
	CONSTRAINT "reservation_quantity" CHECK("reservation_lines"."quantity" > 0)
);
--> statement-breakpoint
CREATE TABLE `reservations` (
	`order_id` text PRIMARY KEY NOT NULL,
	`reserved_at` integer NOT NULL
);
--> statement-breakpoint
CREATE TABLE `stock` (
	`sku` text PRIMARY KEY NOT NULL,
	`on_hand` integer NOT NULL,
	CONSTRAINT "stock_on_hand" CHECK("stock"."on_hand" >= 0)
);
