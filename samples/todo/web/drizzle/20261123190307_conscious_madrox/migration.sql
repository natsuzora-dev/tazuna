CREATE TABLE `notifier_permission_choices` (
	`status` text NOT NULL,
	`at` text NOT NULL,
	CONSTRAINT `notifier_permission_choices_pk` PRIMARY KEY(`status`, `at`)
);
--> statement-breakpoint
CREATE TABLE `notifier_task_changes` (
	`taskId` text NOT NULL,
	`at` text NOT NULL,
	`change` text NOT NULL,
	CONSTRAINT `notifier_task_changes_pk` PRIMARY KEY(`taskId`, `at`, `change`)
);
--> statement-breakpoint
DROP TABLE `notifier_notification_permission`;--> statement-breakpoint
DROP TABLE `notifier_open_tasks`;--> statement-breakpoint
DROP TABLE `notifier_received_events`;