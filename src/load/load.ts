import { readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative, sep } from "node:path";
import { pathToFileURL } from "node:url";
import { parseSync } from "oxc-parser";
import type { z } from "zod";
import type { Malformed } from "../data/malformed.ts";
import { constantsSchema } from "../dsl/constants.ts";
import {
  type ChartSpec,
  type Contract,
  type Definition,
  isDefinition,
  type Named,
  type Place,
  type ServiceDefinition,
} from "../dsl/definition.ts";
import type { Scenario } from "../dsl/scenario.ts";
import { definerService, isContract } from "../dsl/service.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import type { DefinitionStructure } from "../syntax/structure.ts";
import { opaqueCollections } from "./collections.ts";
import { defaultSchemas } from "./defaults.ts";
import type { Found } from "./found.ts";
import { duplicateNames, type NamedExport } from "./names.ts";
import { type DefinerExport, owners } from "./owners.ts";
import { unexportedDefinitions } from "./references.ts";
import { structureOf } from "./structureOf.ts";
import { inexactDelays, unparsableTimes } from "./times.ts";

export interface Constants {
  readonly schema: z.ZodObject;
  readonly values: Readonly<Record<string, unknown>>;
}

type Parsed = ReturnType<typeof parseSync>;

export interface SourceFile {
  readonly file: string;
  readonly service: string;
  readonly text: string;
  readonly program: Parsed["program"];
  readonly comments: Parsed["comments"];
}

export interface Spec {
  readonly root: string;
  /** The definitions, without the definitions and entities that no single service owns. */
  readonly definitions: readonly Named<Definition>[];
  readonly malformed: readonly Found<Malformed>[];
  readonly contracts: readonly Contract[];
  readonly constants: readonly Named<Constants>[];
  readonly scenarios: readonly Named<Scenario>[];
  readonly sources: readonly SourceFile[];
  readonly names: ReadonlyMap<unknown, Named<Definition>>;
  readonly services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>;
  readonly structure: Structure;
}

function tsFiles(dir: string): string[] {
  return readdirSync(dir)
    .sort()
    .flatMap((name) => {
      const path = join(dir, name);
      if (statSync(path).isDirectory()) return name === "__snapshots__" ? [] : tsFiles(path);
      return name.endsWith(".ts") ? [path] : [];
    });
}

export function placeIn(source: Pick<SourceFile, "file" | "text">, offset: number): Place {
  const before = source.text.slice(0, offset).split("\n");
  return { file: source.file, line: before.length, column: (before.at(-1)?.length ?? 0) + 1 };
}

function exportsOf(program: Parsed["program"]): Map<string, number> {
  const exports = new Map<string, number>();
  for (const statement of program.body) {
    if (statement.type !== "ExportNamedDeclaration" || statement.declaration?.type !== "VariableDeclaration") continue;
    for (const declarator of statement.declaration.declarations) {
      const id = declarator.id;
      if (id.type === "Identifier") exports.set(id.name, id.start);
      if (id.type === "ObjectPattern")
        for (const p of id.properties)
          if (p.type === "Property" && p.value.type === "Identifier") exports.set(p.value.name, p.value.start);
    }
  }
  return exports;
}

export function crossServiceImports(spec: Pick<Spec, "sources">) {
  const serviceNames = new Set(spec.sources.map((s) => s.service));
  return spec.sources.flatMap((source) =>
    source.program.body.flatMap((statement) => {
      if (statement.type !== "ImportDeclaration" || !statement.source.value.startsWith("..")) return [];
      const parts = statement.source.value.split("/");
      const other = parts[1];
      if (other === undefined || !serviceNames.has(other) || other === source.service) return [];
      return [{ source, statement, service: other, contract: parts.at(-1) === "contract.ts" }];
    }),
  );
}

export async function loadSpec(root: string): Promise<Spec> {
  const found: Omit<Named<Definition>, "service">[] = [];
  const contracts: Contract[] = [];
  const constants: Named<Constants>[] = [];
  const scenarios: Named<Scenario>[] = [];
  const sources: SourceFile[] = [];
  const definerExports: DefinerExport[] = [];
  const namedExports: NamedExport[] = [];
  for (const path of tsFiles(root)) {
    const file = relative(root, path).split(sep).join("/");
    const service = file.split("/")[0] ?? "";
    const text = readFileSync(path, "utf8");
    const { program, comments } = parseSync(path, text);
    const source: SourceFile = { file, service, text, program, comments };
    sources.push(source);
    const exports = exportsOf(source.program);
    const module: Record<string, unknown> = await import(pathToFileURL(path).href);
    // A module namespace object lists exports in name order; restore source order.
    const written = Object.entries(module).sort(([a], [b]) => (exports.get(a) ?? 0) - (exports.get(b) ?? 0));
    for (const [name, value] of written) {
      const place = placeIn(source, exports.get(name) ?? 0);
      const definer = definerService(value);
      const schema = constantsSchema(value);
      if (isDefinition(value)) {
        namedExports.push({ name, service, place, value });
        if (!found.some((d) => d.definition === value)) found.push({ name, place, definition: value });
      } else if (typeof value === "object" && value !== null && (value as { kind?: string }).kind === "scenario") {
        namedExports.push({ name, service, place, value });
        if (!scenarios.some((s) => s.definition === value))
          scenarios.push({ name, service, place, definition: value as Scenario });
      } else if (definer !== undefined) {
        definerExports.push({ folder: service, definition: definer, place });
      } else if (isContract(value)) {
        contracts.push({ service, place, members: value });
      } else if (schema !== undefined) {
        namedExports.push({ name, service, place, value });
        if (!constants.some((c) => c.definition.values === value))
          constants.push({ name, service, place, definition: { schema, values: value as Constants["values"] } });
      }
    }
  }
  const { services, definitions, malformed } = owners(found, definerExports);
  const names = new Map<unknown, Named<Definition>>(definitions.map((d) => [d.definition, d]));
  const { structure, thrownDefaults } = structureOf(definitions, names, services, contracts, scenarios);
  const opaque = opaqueCollections(definitions, constants);
  const exported = new Set(found.map((d) => d.definition));
  return {
    root,
    definitions,
    malformed: [
      ...duplicateNames(namedExports),
      ...malformed,
      ...unexportedDefinitions(definitions, scenarios, services, contracts, constants, exported),
      ...unparsableTimes(scenarios),
      ...inexactDelays(charts({ definitions, structure })),
      ...opaque,
      ...defaultSchemas(definitions, structure, opaque, thrownDefaults),
    ],
    contracts,
    constants,
    scenarios,
    sources,
    names,
    services,
    structure,
  };
}

export function structured(spec: Pick<Spec, "definitions" | "structure">) {
  return spec.definitions.map((named, i) => ({
    named,
    structure: spec.structure.definitions[i] as DefinitionStructure,
  }));
}

export function charts(spec: Pick<Spec, "definitions" | "structure">) {
  return structured(spec).flatMap(({ named, structure }) =>
    structure.kind === "machine" || structure.kind === "screen"
      ? [{ named, chart: named.definition as unknown as ChartSpec, structure }]
      : [],
  );
}
