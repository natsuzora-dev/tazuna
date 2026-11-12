import { todo } from "@todo/spec/todo";
import { useEffect, useState } from "react";

export const { timeZone } = todo.todoConstants;

export function useNow(): Temporal.Instant | null {
  const [now, setNow] = useState<Temporal.Instant | null>(null);
  useEffect(() => {
    setNow(Temporal.Now.instant());
    const timer = setInterval(() => setNow(Temporal.Now.instant()), 60_000);
    return () => clearInterval(timer);
  }, []);
  return now;
}

export const formatTime = (at: Temporal.ZonedDateTime) =>
  at.toLocaleString("en-US", { hour: "numeric", minute: "2-digit" });

export function formatDateTime(at: Temporal.Instant, now: Temporal.Instant | null) {
  const zoned = at.toZonedDateTimeISO(timeZone);
  const isThisYear = now === null || now.toZonedDateTimeISO(timeZone).year === zoned.year;
  return zoned.toLocaleString("en-US", {
    weekday: "short",
    month: "short",
    day: "numeric",
    ...(isThisYear ? {} : { year: "numeric" }),
    hour: "numeric",
    minute: "2-digit",
  });
}
