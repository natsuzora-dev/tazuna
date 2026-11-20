import assert from "node:assert/strict";
import { relative } from "node:path";
import { after, test } from "node:test";
import { InternalError } from "../src/data/internalError.ts";
import { loadSpec } from "../src/load/load.ts";
import { type Schema, schemaOf, serviceOf } from "../src/service/basic.ts";
import type { Structure } from "../src/spec/structure.generated.ts";
import { mapStateOf } from "../src/spec/structure.ts";
import { groupExamples, runExamples } from "./examples.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

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
            ...(s.held === undefined ? [] : [{ kind: "held", chart: definition, state: s.name } as const]),
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
