import type { todo } from "@todo/spec/todo";
import { eq, isNotNull, isNull } from "drizzle-orm";
import type { z } from "zod";
import { db } from "../db/index.server.ts";
import { settings, tasks } from "../db/schema.ts";

export type Filter = z.output<typeof todo.tasks.input.filter>;

const completion = { open: isNull(tasks.completedAt), completed: isNotNull(tasks.completedAt), all: undefined };

export function readTasks({ filter }: { readonly filter: Filter }) {
  return {
    tasks: db
      .select({ taskId: tasks.id, title: tasks.title, dueAt: tasks.dueAt, completedAt: tasks.completedAt })
      .from(tasks)
      .where(completion[filter])
      .all(),
  };
}

export function readTaskDetail({ taskId }: { readonly taskId: string }) {
  const task = db.select().from(tasks).where(eq(tasks.id, taskId)).get();
  return {
    task:
      task === undefined
        ? null
        : {
            title: task.title,
            isCompleted: task.completedAt !== null,
            dueAt: task.dueAt,
            createdAt: task.createdAt,
            remindAt: task.remindAt,
          },
  };
}

export function readReminderSettings() {
  return { shouldRemind: db.select().from(settings).get()?.shouldRemind ?? true };
}
