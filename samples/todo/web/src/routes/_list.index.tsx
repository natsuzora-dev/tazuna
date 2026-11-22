import type { InferRouterInputs, InferRouterOutputs } from "@orpc/server";
import { useIsMutating, useMutation, useQuery } from "@tanstack/react-query";
import { createFileRoute, getRouteApi, Link } from "@tanstack/react-router";
import { todo } from "@todo/spec/todo";
import { useRef } from "react";
import { orpc } from "../orpc/client.ts";
import type { router } from "../orpc/router.ts";
import { formatDateTime, formatTime, useNow, zoned } from "../time.ts";

export const Route = createFileRoute("/_list/")({ component: TaskList });

const list = getRouteApi("/_list");

type Filter = InferRouterInputs<typeof router>["todo"]["tasks"]["filter"];
type TasksOutput = InferRouterOutputs<typeof router>["todo"]["tasks"] extends AsyncIterable<infer T> ? T : never;
type Task = TasksOutput["tasks"][number];

const filterLabels: Record<Filter, string> = { open: "Open", completed: "Completed", all: "All" };

type Group = "late" | "today" | "later" | "none" | "completed";
const groupLabels = new Map<Group, string>([
  ["late", "Overdue"],
  ["today", "Today"],
  ["later", "Upcoming"],
  ["none", "No due date"],
  ["completed", "Completed"],
]);

function groupOf({ dueAt, completedAt }: Task, now: number): Group {
  if (completedAt !== null) return "completed";
  if (dueAt === null) return "none";
  if (dueAt <= now) return "late";
  return zoned(dueAt).toPlainDate().equals(zoned(now).toPlainDate()) ? "today" : "later";
}

const byDue = (a: Task, b: Task) => (a.dueAt === null || b.dueAt === null ? 0 : a.dueAt - b.dueAt);

function TaskList() {
  const { filter = "open" } = list.useSearch();
  const navigate = list.useNavigate();
  const { data: reminders } = useQuery(orpc.todo.reminderSettings.experimental_liveOptions({ input: {} }));
  const { data: shown } = useQuery(orpc.todo.tasks.experimental_liveOptions({ input: { filter } }));
  const now = useNow();
  const add = useMutation(orpc.todo.addTask.mutationOptions());
  const toggleReminders = useMutation(orpc.todo.changeReminders.mutationOptions());
  // While any request waits for its answer, the screen takes no operation that sends another.
  const isBusy = useIsMutating() > 0;
  const titleInput = useRef<HTMLInputElement>(null);

  return (
    <section aria-label="Task list" aria-busy={isBusy}>
      <header className="bar">
        <h1>Tasks</h1>
        <label className="switch">
          Reminders
          <input
            type="checkbox"
            // biome-ignore lint/a11y/useAriaPropsForRole: ARIA in HTML forbids aria-checked on a checkbox input
            role="switch"
            data-testid="remindersToggle"
            disabled={isBusy || reminders === undefined}
            checked={reminders?.shouldRemind ?? false}
            onChange={(e) => toggleReminders.mutate({ shouldRemind: e.currentTarget.checked })}
          />
        </label>
      </header>
      <form
        className="add"
        onSubmit={(e) => {
          e.preventDefault();
          const form = e.currentTarget;
          add.mutate(
            { taskId: crypto.randomUUID(), title: String(new FormData(form).get("title")) },
            {
              onSuccess: () => form.reset(),
              onSettled: () => titleInput.current?.focus(),
            },
          );
        }}
      >
        <input
          ref={titleInput}
          name="title"
          data-testid="add"
          aria-label="New task"
          placeholder="New task"
          autoComplete="off"
          required
          disabled={isBusy}
        />
        <button type="submit" className="button" disabled={isBusy}>
          Add
        </button>
      </form>
      <fieldset className="segmented" data-testid="filter" aria-label="Filter">
        {todo.tasks.input.filter.options.map((value) => (
          <label key={value}>
            <input
              type="radio"
              name="filter"
              value={value}
              checked={filter === value}
              onChange={() => navigate({ search: (prev) => ({ ...prev, filter: value }) })}
            />
            {filterLabels[value]}
          </label>
        ))}
      </fieldset>
      {shown != null && now !== null && <Groups tasks={shown.tasks} now={now} isBusy={isBusy} />}
    </section>
  );
}

function Groups({ tasks, now, isBusy }: { tasks: readonly Task[]; now: number; isBusy: boolean }) {
  if (tasks.length === 0) return <p className="status">No tasks</p>;
  const grouped = Map.groupBy(tasks, (t) => groupOf(t, now));
  return [...groupLabels].flatMap(([group, label]) => {
    const members = grouped.get(group);
    if (members === undefined) return [];
    return [
      <section key={group} aria-label={label}>
        <h2 className={group === "late" ? "group is-late" : "group"}>{label}</h2>
        <ul className="tasks">
          {members.toSorted(byDue).map((task) => (
            <Row key={task.taskId} task={task} group={group} now={now} isBusy={isBusy} />
          ))}
        </ul>
      </section>,
    ];
  });
}

function Row({
  task: { taskId, title, dueAt, completedAt },
  group,
  now,
  isBusy,
}: {
  task: Task;
  group: Group;
  now: number;
  isBusy: boolean;
}) {
  const complete = useMutation(orpc.todo.completeTask.mutationOptions());
  const reopen = useMutation(orpc.todo.reopenTask.mutationOptions());
  const isCompleted = completedAt !== null;
  return (
    <li className={isCompleted ? "task is-completed" : "task"}>
      <button
        type="button"
        className="check"
        data-testid={isCompleted ? "reopen" : "complete"}
        aria-label={isCompleted ? `Mark ${title} as incomplete` : `Mark ${title} as complete`}
        disabled={isBusy}
        onClick={() => (isCompleted ? reopen : complete).mutate({ taskId })}
      />
      <Link
        className="task-title"
        to="/tasks/$taskId"
        params={{ taskId }}
        state={{ placeholderTitle: title }}
        data-testid="openTask"
        disabled={isBusy}
      >
        {title}
      </Link>
      {dueAt !== null && (
        <span className={`chip is-${group}`}>{group === "today" ? formatTime(dueAt) : formatDateTime(dueAt, now)}</span>
      )}
    </li>
  );
}
