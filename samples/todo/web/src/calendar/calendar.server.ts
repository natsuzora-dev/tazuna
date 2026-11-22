import type { calendar } from "@todo/spec/calendar";
import type { z } from "zod";
import { timeZone, zoned } from "../time.ts";

type NextBusinessDay = typeof calendar.nextBusinessDay;

export type CalendarResult =
  | ({ readonly ok: true } & z.output<z.ZodObject<NextBusinessDay["output"]>>)
  | { readonly ok: false; readonly error: "unavailable" };

const weekend = [6, 7];

export async function nextBusinessDay({
  after,
}: z.output<z.ZodObject<NextBusinessDay["input"]>>): Promise<CalendarResult> {
  let day = zoned(after).toPlainDate().add({ days: 1 });
  while (weekend.includes(day.dayOfWeek)) day = day.add({ days: 1 });
  return { ok: true, startsAt: day.toZonedDateTime(timeZone).epochMilliseconds };
}
