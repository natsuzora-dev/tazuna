import { bag, ref } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { query, Settings, Task } from "./data.ts";

const Filter = z.enum(["open", "completed", "all"]).meta({
  description:
    "open selects the tasks that are not completed, completed selects the completed tasks, and all selects every task",
});

const matches = (filter: z.infer<typeof Filter>, completedAt: Temporal.Instant | null) =>
  filter === "all" || (filter === "open" ? completedAt === null : completedAt !== null);

// tasks does not group by due date: overdue or due today changes with time alone, but a subscription is recomputed
// only after a message, so the list screen groups and sorts.
export const tasks = query({
  input: { filter: Filter },
  output: {
    tasks: bag(
      z.object({
        taskId: ref(Task),
        title: Task.fields.title,
        dueAt: Task.fields.dueAt,
        completedAt: Task.fields.completedAt,
      }),
    ),
  },
  ensures: {
    matchesFilter: ({ input, output, records }) =>
      output.tasks.every((t) => matches(input.filter, records.Task.get(t.taskId)?.completedAt ?? null)),
  },
}).resolve(({ input, records }) => ({
  tasks: records.Task.filter((t) => matches(input.filter, t.completedAt)).map((t) => ({
    taskId: t.id,
    title: t.title,
    dueAt: t.dueAt,
    completedAt: t.completedAt,
  })),
}));

export const taskDetail = query({
  input: { taskId: ref(Task) },
  output: {
    task: z
      .object({
        title: Task.fields.title,
        isCompleted: z.boolean(),
        dueAt: Task.fields.dueAt,
        createdAt: Task.fields.createdAt,
        remindAt: Task.fields.remindAt,
      })
      .nullable(),
  },
}).resolve(({ input, records }) => {
  const task = records.Task.get(input.taskId);
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
});

export const reminderSettings = query({
  output: { shouldRemind: Settings.fields.shouldRemind.unwrap() },
}).resolve(({ records }) => ({ shouldRemind: records.Settings.shouldRemind }));
