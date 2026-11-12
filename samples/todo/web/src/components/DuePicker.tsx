import { todo } from "@todo/spec/todo";
import { useState } from "react";
import { formatDateTime, timeZone } from "../time.ts";

const localDateTime = (at: Temporal.Instant) =>
  at.toZonedDateTimeISO(timeZone).toPlainDateTime().toString({ smallestUnit: "minute" });

const untilOf = (now: Temporal.Instant) =>
  now.toZonedDateTimeISO(timeZone).add(todo.todoConstants.dueAheadLimit).toInstant();

function suggestionOf(now: Temporal.Instant): Temporal.Instant {
  const nextHour = now
    .toZonedDateTimeISO(timeZone)
    .round({ smallestUnit: "hour", roundingMode: "floor" })
    .add({ hours: 1 })
    .toInstant();
  const until = untilOf(now);
  return Temporal.Instant.compare(nextHour, until) <= 0 ? nextHour : until;
}

export function DuePicker({
  id,
  dueAt,
  onChoose,
  onCollapse,
}: {
  id: string;
  dueAt: Temporal.Instant | null;
  onChoose: (dueAt: Temporal.Instant | null) => void;
  onCollapse: () => void;
}) {
  const [openedAt] = useState(() => Temporal.Now.instant());
  const [error, setError] = useState<string | null>(null);

  const choose = (value: string) => {
    if (dueAt !== null && value === localDateTime(dueAt)) return onCollapse();
    const chosen = Temporal.PlainDateTime.from(value).toZonedDateTime(timeZone).toInstant();
    const now = Temporal.Now.instant();
    const until = untilOf(now);
    if (Temporal.Instant.compare(chosen, now) <= 0) setError("Choose a time in the future");
    else if (Temporal.Instant.compare(chosen, until) > 0)
      setError(`Choose a due date on or before ${formatDateTime(until, now)}`);
    else onChoose(chosen);
  };

  return (
    <div className="picker" id={id}>
      <input
        type="datetime-local"
        className="picker-input"
        data-testid="dueChoose"
        aria-label="Date and time"
        defaultValue={localDateTime(dueAt ?? suggestionOf(openedAt))}
        min={localDateTime(openedAt)}
        max={localDateTime(untilOf(openedAt))}
        onKeyDown={(e) => {
          if (e.key === "Enter") e.currentTarget.blur();
        }}
        onBlur={(e) => {
          const { value } = e.currentTarget;
          if (value !== "") choose(value);
        }}
      />
      {error !== null && (
        <p className="error" role="alert">
          {error}
        </p>
      )}
      {dueAt !== null && (
        <button type="button" className="link is-danger" data-testid="dueClear" onClick={() => onChoose(null)}>
          Remove due date
        </button>
      )}
    </div>
  );
}
