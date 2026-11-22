import { useEffect, useState } from "react";

/** The app shows and decides calendar days in Tokyo; the spec holds instants as milliseconds and knows no zone. */
export const timeZone = "Asia/Tokyo";

/** The instant `ms` in the app's time zone. */
export const zoned = (ms: number) => Temporal.Instant.fromEpochMilliseconds(ms).toZonedDateTimeISO(timeZone);

export function useNow(): number | null {
  const [now, setNow] = useState<number | null>(null);
  useEffect(() => {
    setNow(Date.now());
    const timer = setInterval(() => setNow(Date.now()), 60_000);
    return () => clearInterval(timer);
  }, []);
  return now;
}

export const formatTime = (at: number) => zoned(at).toLocaleString("en-US", { hour: "numeric", minute: "2-digit" });

export function formatDateTime(at: number, now: number | null) {
  const day = zoned(at);
  const isThisYear = now === null || zoned(now).year === day.year;
  return day.toLocaleString("en-US", {
    weekday: "short",
    month: "short",
    day: "numeric",
    ...(isThisYear ? {} : { year: "numeric" }),
    hour: "numeric",
    minute: "2-digit",
  });
}
