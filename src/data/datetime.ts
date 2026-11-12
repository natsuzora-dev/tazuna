import { z } from "zod";

/** An instant. For dates, convert to a `Temporal.ZonedDateTime` with an explicit time zone. */
export const datetime = z.codec(z.iso.datetime({ offset: true }), z.instanceof(Temporal.Instant), {
  decode: (text) => Temporal.Instant.from(text),
  encode: (instant) => instant.toString(),
});

/** A calendar date. Compare with `Temporal.PlainDate.compare` or `equals`, not `===`. */
export const date = z.codec(z.iso.date(), z.instanceof(Temporal.PlainDate), {
  decode: (text) => Temporal.PlainDate.from(text),
  encode: (plainDate) => plainDate.toString(),
});

/** A length of time, written as an ISO 8601 duration ("PT10S"). */
export const duration = z.codec(z.iso.duration(), z.instanceof(Temporal.Duration), {
  decode: (text) => Temporal.Duration.from(text),
  encode: (length) => length.toString(),
});

/** An IANA time zone name ("Asia/Tokyo"). */
export const timeZone = z.string().refine((name) => Intl.supportedValuesOf("timeZone").includes(name), {
  error: "not an IANA time zone name",
});

/**
 * A deadline's delay: hours, minutes, seconds and milliseconds, the units that Instant.add takes, down to the
 * millisecond that the run counts; or a Temporal.Duration, such as a `duration` constant.
 */
export type Delay =
  | {
      readonly hours?: number;
      readonly minutes?: number;
      readonly seconds?: number;
      readonly milliseconds?: number;
      readonly years?: never;
      readonly months?: never;
      readonly weeks?: never;
      readonly days?: never;
      readonly microseconds?: never;
      readonly nanoseconds?: never;
    }
  | Temporal.Duration;
