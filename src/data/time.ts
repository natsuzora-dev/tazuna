import { z } from "zod";

/** An instant: milliseconds since 1970-01-01T00:00:00Z. Compare with `<` and add a `duration` with `+`. */
export const instant = z.int();

/** A length of time in milliseconds. */
export const duration = z.int();

declare const dateBrand: unique symbol;
interface DateBrand {
  readonly [dateBrand]: true;
}

/** A calendar date label, "YYYY-MM-DD", which names a day in no time zone. */
export type DateLabel = string & DateBrand;

/** A calendar date label. Compare with `<` and `===`, and move by days with `addDays`. */
export const date: z.ZodType<DateLabel, string> = z.iso.date() as never;

/** Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's days_from_civil), as Lean computes it. */
function daysFromCivil(year: number, month: number, day: number): number {
  const y = month <= 2 ? year - 1 : year;
  const era = Math.floor(y / 400);
  const yoe = y - era * 400;
  const doy = Math.floor((153 * (month > 2 ? month - 3 : month + 9) + 2) / 5) + day - 1;
  const doe = yoe * 365 + Math.floor(yoe / 4) - Math.floor(yoe / 100) + doy;
  return era * 146097 + doe - 719468;
}

const civil = /^(\d{4})-(\d{2})-(\d{2})/;

/** The days since 1970-01-01 of the date at the start of `text`, or undefined when it names no day. */
function daysOf(text: string): number | undefined {
  const m = civil.exec(text);
  if (m === null) return undefined;
  const [year, month, day] = [Number(m[1]), Number(m[2]), Number(m[3])];
  const days = daysFromCivil(year, month, day);
  return month >= 1 && month <= 12 && day >= 1 && day <= 31 && labelOf(days) === m[0] ? days : undefined;
}

/** The label of the day `days` after 1970-01-01, or undefined outside years 0000 through 9999. */
function labelOf(days: number): string | undefined {
  const d = new Date(0);
  d.setUTCFullYear(1970, 0, 1 + days);
  const year = d.getUTCFullYear();
  if (!(year >= 0 && year <= 9999)) return undefined;
  const two = (n: number) => String(n).padStart(2, "0");
  return `${String(year).padStart(4, "0")}-${two(d.getUTCMonth() + 1)}-${two(d.getUTCDate())}`;
}

/** The date `days` days after `label`. It throws a RangeError outside years 0000 through 9999. */
export function addDays(label: DateLabel, days: number): DateLabel {
  const from = daysOf(label);
  const moved = from === undefined || !Number.isSafeInteger(days) ? undefined : labelOf(from + days);
  if (moved === undefined) throw new RangeError(`addDays(${label}, ${days}) names no date in years 0000 through 9999`);
  return moved as DateLabel;
}

const isoInstant = /^\d{4}-\d{2}-\d{2}T(\d{2}):(\d{2}):(\d{2})(?:\.(\d{1,3}))?(?:Z|([+-])(\d{2}):(\d{2}))$/;

/**
 * The instant of an ISO 8601 text with seconds and `Z` or a fixed offset, such as "2026-10-25T10:00:00+09:00", for
 * scenarios to write times readably. It reads the offset by arithmetic and knows no time zone. It throws a RangeError on
 * any other text.
 */
export function parseInstant(text: string): number {
  const m = isoInstant.exec(text);
  const days = daysOf(text);
  if (m === null || days === undefined) throw new RangeError(`${text} is no ISO instant with seconds and Z or ±HH:MM`);
  const [hours, minutes, seconds] = [Number(m[1]), Number(m[2]), Number(m[3])];
  const offset = m[5] === undefined ? 0 : (m[5] === "-" ? -1 : 1) * (Number(m[6]) * 60 + Number(m[7]));
  if (hours > 23 || minutes > 59 || seconds > 59 || Number(m[6] ?? 0) > 23 || Number(m[7] ?? 0) > 59)
    throw new RangeError(`${text} is no ISO instant with seconds and Z or ±HH:MM`);
  const ms = Number((m[4] ?? "").padEnd(3, "0"));
  return (((days * 24 + hours) * 60 + minutes - offset) * 60 + seconds) * 1000 + ms;
}
