import { todo } from "@todo/spec/todo";
import { useState } from "react";
import { formatDateTime, timeZone, zoned } from "../time.ts";

const localDateTime = (at: number) => zoned(at).toPlainDateTime().toString({ smallestUnit: "minute" });

const untilOf = (now: number) => now + todo.todoConstants.dueAheadLimit;

function suggestionOf(now: number): number {
  const nextHour = zoned(now)
    .round({ smallestUnit: "hour", roundingMode: "floor" })
    .add({ hours: 1 }).epochMilliseconds;
  return Math.min(nextHour, untilOf(now));
}

export function DuePicker({
  id,
  dueAt,
  onChoose,
  onCollapse,
}: {
  id: string;
  dueAt: number | null;
  onChoose: (dueAt: number | null) => void;
  onCollapse: () => void;
}) {
  const [openedAt] = useState(() => Date.now());
  const [error, setError] = useState<string | null>(null);

  const choose = (value: string) => {
    if (dueAt !== null && value === localDateTime(dueAt)) return onCollapse();
    const chosen = Temporal.PlainDateTime.from(value).toZonedDateTime(timeZone).epochMilliseconds;
    const now = Date.now();
    const until = untilOf(now);
    if (chosen <= now) setError("Choose a time in the future");
    else if (chosen > until) setError(`Choose a due date on or before ${formatDateTime(until, now)}`);
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
