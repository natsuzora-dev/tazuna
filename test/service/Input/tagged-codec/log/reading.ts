import { instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

const fromCelsius = z.codec(z.number(), z.number(), { decode: (c) => c + 273, encode: (k) => k - 273 });
const fromFahrenheit = z.codec(z.number(), z.number(), {
  decode: (f) => ((f + 459) * 5) / 9,
  encode: (k) => (k * 9) / 5 - 459,
});

/** A reading in kelvin, written in the unit that its tag names. */
export const reading = z.discriminatedUnion("unit", [
  z.object({ unit: z.literal("celsius"), kelvin: fromCelsius }),
  z.object({ unit: z.literal("fahrenheit"), kelvin: fromFahrenheit, at: instant }),
]);
