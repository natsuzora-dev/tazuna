import { constants, instant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event, contract } = service({ name: "todo", description: "Keep the tasks" });

const celsius = z.codec(z.number(), z.number(), { decode: (c) => c + 273.15, encode: (k) => k - 273.15 });
const fahrenheit = z.codec(z.number(), z.number(), {
  decode: (f) => ((f - 32) * 5) / 9 + 273.15,
  encode: (k) => ((k - 273.15) * 9) / 5 + 32,
});

export const readingTaken = event({
  payload: {
    kelvin: z.union([celsius, fahrenheit]),
    due: z.union([instant, z.null()]),
    deep: z.union([z.object({ at: instant }), z.object({ count: z.number() })]),
    nested: z.discriminatedUnion("unit", [
      z.object({ unit: z.literal("celsius"), kelvin: z.union([celsius, z.null()]) }),
      z.object({ unit: z.literal("none") }),
    ]),
    outer: z.union([z.union([celsius, z.string()]), z.boolean()]),
    tagged: z.discriminatedUnion("unit", [
      z.object({ unit: z.literal("celsius"), kelvin: celsius }),
      z.object({ unit: z.literal("fahrenheit"), kelvin: fahrenheit }),
    ]),
    plain: z.union([z.string(), z.number()]),
  },
});

export const todo = contract({ readingTaken });

export const limits = constants({
  service: "todo",
  schema: z.strictObject({ most: z.union([celsius, z.string()]) }),
  values: { most: 3 },
});
