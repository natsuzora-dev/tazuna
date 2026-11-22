import { useIsMutating, useMutation, useQuery } from "@tanstack/react-query";
import { createFileRoute, Link, useLocation, useNavigate } from "@tanstack/react-router";
import { todo } from "@todo/spec/todo";
import { type MouseEvent, useState } from "react";
import { DuePicker } from "../components/DuePicker.tsx";
import { client, orpc } from "../orpc/client.ts";
import { useEvents } from "../orpc/useEvents.ts";
import { formatDateTime, useNow } from "../time.ts";

declare module "@tanstack/react-router" {
  interface HistoryState {
    placeholderTitle?: string;
  }
}

export const Route = createFileRoute("/_list/tasks/$taskId")({ component: TaskDetail });

const subscribeTodoEvents = () => client.todo.todoEvents(undefined, { context: { retry: Number.POSITIVE_INFINITY } });

function TaskDetail() {
  const { taskId } = Route.useParams();
  const placeholderTitle = useLocation({ select: (location) => location.state.placeholderTitle ?? "" });
  const navigate = useNavigate();
  const close = () => navigate({ to: "/" });
  const [isDeleting, setIsDeleting] = useState(false);
  const remove = useMutation(orpc.todo.deleteTask.mutationOptions({ onMutate: () => setIsDeleting(true) }));
  const isBusy = useIsMutating() > 0;

  useEvents(subscribeTodoEvents, (event) => {
    if (event.name === "taskDeleted" && event.payload.taskId === taskId) void close();
  });

  return (
    <section aria-label="Task details" aria-busy={isBusy}>
      {/* While a request waits for its answer, the screen neither closes nor deletes the task. */}
      <Link to="/" className="back" data-testid="close" disabled={isBusy}>
        ‹ Tasks
      </Link>
      {isDeleting ? (
        <p className="status">Deleting…</p>
      ) : (
        <Editing
          taskId={taskId}
          placeholderTitle={placeholderTitle}
          onDelete={() =>
            remove.mutate({ taskId }, { onSuccess: () => void close(), onError: () => setIsDeleting(false) })
          }
        />
      )}
    </section>
  );
}

const keepFocusInPicker = (e: MouseEvent) => e.preventDefault();

function Editing({
  taskId,
  placeholderTitle,
  onDelete,
}: {
  taskId: string;
  placeholderTitle: string;
  onDelete: () => void;
}) {
  const { data: detail } = useQuery(orpc.todo.taskDetail.experimental_liveOptions({ input: { taskId } }));
  const now = useNow();
  const task = detail?.task ?? null;
  const [draft, setDraft] = useState<string | null>(null);
  const [draftOf, setDraftOf] = useState(task?.title);
  if (draftOf !== task?.title) {
    setDraftOf(task?.title);
    setDraft(null);
  }
  const rename = useMutation(orpc.todo.renameTask.mutationOptions());
  const complete = useMutation(orpc.todo.completeTask.mutationOptions());
  const reopen = useMutation(orpc.todo.reopenTask.mutationOptions());
  const changeDueAt = useMutation(orpc.todo.changeDue.mutationOptions());
  const [due, setDue] = useState<"collapsed" | "expanded" | "changing">("collapsed");
  const isCompleted = task?.isCompleted === true;
  const isBusy = useIsMutating() > 0;

  const commitTitle = (title: string) => {
    if (rename.isPending || title === task?.title) return;
    if (!todo.TaskTitle.safeParse(title).success) return setDraft(null);
    rename.mutate({ taskId, title }, { onError: () => setDraft(null) });
  };
  const chooseDue = (dueAt: number | null) => {
    setDue("changing");
    changeDueAt.mutate({ taskId, dueAt }, { onSettled: () => setDue("collapsed") });
  };

  return (
    <>
      <div className={isCompleted ? "head is-completed" : "head"}>
        <button
          type="button"
          className="check"
          data-testid={isCompleted ? "reopen" : "complete"}
          aria-label={isCompleted ? "Mark as incomplete" : "Mark as complete"}
          disabled={task === null || complete.isPending || reopen.isPending}
          onClick={() => (isCompleted ? reopen : complete).mutate({ taskId })}
        />
        <input
          className="title-input"
          data-testid="rename"
          aria-label="Title"
          value={draft ?? task?.title ?? placeholderTitle}
          onChange={(e) => setDraft(e.currentTarget.value)}
          onKeyDown={(e) => {
            if (e.key === "Enter") e.currentTarget.blur();
          }}
          onBlur={(e) => commitTitle(e.currentTarget.value)}
        />
      </div>
      <div className="item">
        <button
          type="button"
          className="row is-toggle"
          data-testid="dueToggle"
          aria-expanded={due === "expanded"}
          aria-controls="due-picker"
          disabled={due === "changing"}
          onMouseDown={keepFocusInPicker}
          onClick={() => setDue(due === "expanded" ? "collapsed" : "expanded")}
        >
          <span className="row-name">Due</span>
          <span>{task?.dueAt == null ? "None" : formatDateTime(task.dueAt, now)}</span>
          <span className="caret" aria-hidden="true">
            ▾
          </span>
        </button>
        {due === "expanded" && (
          <DuePicker
            id="due-picker"
            dueAt={task?.dueAt ?? null}
            onChoose={chooseDue}
            onCollapse={() => setDue("collapsed")}
          />
        )}
      </div>
      <div className="item row">
        <span className="row-name">Reminder</span>
        <span>{task?.remindAt == null ? "None" : formatDateTime(task.remindAt, now)}</span>
      </div>
      <div className="item row">
        <span className="row-name">Created</span>
        <span>{task === null ? "" : formatDateTime(task.createdAt, now)}</span>
      </div>
      <button type="button" className="link is-danger delete" data-testid="delete" disabled={isBusy} onClick={onDelete}>
        Delete task
      </button>
    </>
  );
}
