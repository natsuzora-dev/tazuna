CREATE TABLE `command_answers` (
	`key` text PRIMARY KEY,
	`request` text NOT NULL,
	`answer` text NOT NULL
);
--> statement-breakpoint
CREATE TABLE `notifier_notification_permission` (
	`id` integer PRIMARY KEY,
	`status` text NOT NULL
);
--> statement-breakpoint
CREATE TABLE `notifier_open_tasks` (
	`taskId` text PRIMARY KEY
);
--> statement-breakpoint
CREATE TABLE `notifier_received_events` (
	`id` text PRIMARY KEY
);
--> statement-breakpoint
CREATE TABLE `settings` (
	`id` integer PRIMARY KEY,
	`shouldRemind` integer NOT NULL
);
--> statement-breakpoint
CREATE TABLE `tasks` (
	`id` text PRIMARY KEY,
	`title` text NOT NULL,
	`createdAt` text NOT NULL,
	`completedAt` text,
	`dueAt` text,
	`remindAt` text,
	`reminderDecision` text NOT NULL
);
