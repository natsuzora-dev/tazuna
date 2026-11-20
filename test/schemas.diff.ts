import assert from "node:assert/strict";
import { relative } from "node:path";
import { after, test } from "node:test";
import fc from "fast-check";
import { InternalError } from "../src/data/internalError.ts";
import { loadSpec } from "../src/load/load.ts";
import { instant } from "../src/scenario/lower.ts";
import { type Schema, schemaOf, serviceOf } from "../src/service/basic.ts";
import type { Structure } from "../src/spec/structure.generated.ts";
import { mapStateOf } from "../src/spec/structure.ts";
import { groupExamples, runExamples } from "./examples.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const digits = (n: number) => fc.stringMatching(new RegExp(`^\\d{${n}}$`));
const pick = <T>(...xs: T[]) => fc.constantFrom(...xs);

/** Every schema that the structure of `service` names, and some that it does not. */
function schemasOf(structure: Structure, service: string): Schema[] {
  const own = structure.definitions.filter((d) => d.service === service);
  return own.flatMap((d): Schema[] => {
    const definition = { service: d.service, name: d.name };
    switch (d.kind) {
      case "command":
      case "query":
        return [
          { kind: "input", definition },
          { kind: "output", definition },
        ];
      case "event":
        return [{ kind: "payload", event: definition }];
      case "entity":
        return [{ kind: "record", entity: definition }];
      case "machine":
      case "screen":
        return [
          { kind: "input", definition },
          { kind: "output", definition },
          { kind: "context", chart: definition },
          ...(d.kind === "screen"
            ? [...Object.keys(d.controls), "absent"].map(
                (control): Schema => ({ kind: "control", screen: definition, control }),
              )
            : []),
          ...d.states.flatMap((s): Schema[] => [
            ...Object.keys((s.held?.schema as { properties?: object } | undefined)?.properties ?? {}).map(
              (name): Schema => ({ kind: "held", chart: definition, state: s.name, name }),
            ),
            ...(mapStateOf(s) === undefined
              ? []
              : [
                  { kind: "mapContext", chart: definition, map: s.name } as const,
                  { kind: "mapKey", chart: definition, map: s.name } as const,
                ]),
          ]),
        ];
      default:
        return [{ kind: "payload", event: definition }];
    }
  });
}

const structures = (
  await Promise.all(
    [...groupExamples("validation"), ...runExamples()].map(async (root) => {
      const loaded = await loadSpec(root);
      return loaded.kind === "structured"
        ? [{ name: relative(import.meta.dirname, root), structure: loaded.spec.structure }]
        : [];
    }),
  )
).flat();

test("TS reads the time of a start or clock line as Lean's scenarioTime? does", () => {
  const time = fc
    .tuple(
      pick("2026", "0000", "9999", "1970", "2024"),
      pick("01", "02", "12", "13", "00"),
      pick("01", "28", "29", "30", "31", "32"),
      pick("00", "09", "23", "24"),
      pick("00", "59", "60"),
      pick("", ":00", ":59", ":60"),
      fc.oneof(pick("", ".", ".5", ".123", ".000000", ".0001", ".001000", ".123456789", ".1234567890"), digits(4)),
      pick("Z", "z", "+09:00", "-23:59", "+24:00", "+0900", "+09", ""),
    )
    .map(
      ([y, mo, d, h, mi, s, f, o]) =>
        `${y}-${mo}-${d}T${h}:${mi}${s}${f.startsWith(".") || f === "" ? f : `.${f}`}${o}`,
    );
  fc.assert(
    fc.property(time, (text) => {
      assert.equal(instant(text), lean.scenarioTime(text));
    }),
    { numRuns: 400 },
  );
});

for (const { name, structure } of structures)
  test(`${name}: TS reads each schema from the structure as Lean's Service.schemaOf does`, () => {
    for (const service of new Set(structure.definitions.map((d) => d.service))) {
      const st = serviceOf(structure, service);
      for (const schema of schemasOf(structure, service)) {
        let ts: unknown;
        try {
          ts = schemaOf(st, schema);
        } catch (error) {
          if (!(error instanceof InternalError)) throw error;
        }
        assert.deepEqual(ts, lean.schemaOf(structure, service, schema), JSON.stringify(schema));
      }
    }
  });
