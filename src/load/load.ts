import { existsSync, readdirSync, readFileSync, realpathSync, statSync } from "node:fs";
import { dirname, join, posix, relative, resolve, sep } from "node:path";
import { pathToFileURL } from "node:url";
import { parseSync } from "oxc-parser";
import type { z } from "zod";
import { InternalError } from "../data/internalError.ts";
import type { Malformed } from "../data/malformed.ts";
import { chartOf } from "../dsl/chart.ts";
import { constantsSchema, constantsService } from "../dsl/constants.ts";
import {
  type Contract,
  type Definition,
  isDefinition,
  type Named,
  type Place,
  type ServiceDefinition,
} from "../dsl/definition.ts";
import { contractService, definerService, isContract } from "../dsl/service.ts";
import { isScenarioDefinition, type ScenarioDefinition, scenarioService } from "../scenario/define.ts";
import type { Structure } from "../spec/structure.generated.ts";
import type { DefinitionStructure } from "../spec/structure.ts";
import { opaqueCollections } from "./collections.ts";
import { defaultSchemas } from "./defaults.ts";
import type { Found } from "./found.ts";
import { caseCollisions, duplicateNames, type NamedExport, reservedNames } from "./names.ts";
import { type DefinerExport, owners } from "./owners.ts";
import { unexportedDefinitions } from "./references.ts";
import { type LoadedScenario, loadScenarios } from "./scenarios.ts";
import { misplacedSelfRefs } from "./selfRefs.ts";
import { structureOf } from "./structureOf.ts";
import { unrepresentableSchemas } from "./unrepresentable.ts";

interface Constants {
  readonly schema: z.ZodObject;
  readonly values: Readonly<Record<string, unknown>>;
}

type Parsed = ReturnType<typeof parseSync>;

export interface SourceFile {
  readonly file: string;
  readonly text: string;
  readonly program: Parsed["program"];
  readonly comments: Parsed["comments"];
}

export interface Spec {
  readonly root: string;
  /** The definitions, without the definitions and entities that no single service owns. */
  readonly definitions: readonly Named<Definition>[];
  readonly contracts: readonly Contract[];
  readonly constants: readonly Named<Constants>[];
  readonly scenarios: readonly Named<LoadedScenario>[];
  readonly sources: readonly SourceFile[];
  /** The local modules outside root that sources import, directly or through each other. */
  readonly imported: readonly SourceFile[];
  readonly imports: readonly ServiceImport[];
  readonly names: ReadonlyMap<unknown, Named<Definition>>;
  readonly services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>;
  readonly structure: Structure;
}

const skippedFolders = new Set(["__snapshots__", "node_modules"]);

/** The spec files under `dir`, walking each folder once however many symlinks lead to it. */
function tsFiles(dir: string, visited = new Set([realpathSync(dir)])): string[] {
  return readdirSync(dir)
    .sort()
    .flatMap((name) => {
      const path = join(dir, name);
      const stat = statSync(path, { throwIfNoEntry: false });
      if (stat === undefined) return [];
      if (!stat.isDirectory()) return name.endsWith(".ts") && !name.endsWith(".d.ts") ? [path] : [];
      const real = realpathSync(path);
      if (skippedFolders.has(name) || visited.has(real)) return [];
      visited.add(real);
      return tsFiles(path, visited);
    });
}

function parsed(path: string, file: string): SourceFile {
  const text = readFileSync(path, "utf8");
  const { program, comments } = parseSync(path, text);
  return { file, text, program, comments };
}

const moduleFile = /\.[cm]?[jt]sx?$/;

/** The modules outside `root` that `sources` import by a relative path, directly or through each other. */
function importedOutside(root: string, sources: readonly SourceFile[]): SourceFile[] {
  const imported: SourceFile[] = [];
  const visit = (source: SourceFile): void => {
    for (const statement of source.program.body) {
      const from =
        (statement.type === "ImportDeclaration" && statement.importKind !== "type") ||
        ((statement.type === "ExportNamedDeclaration" || statement.type === "ExportAllDeclaration") &&
          statement.exportKind !== "type")
          ? statement.source?.value
          : undefined;
      if (from === undefined || !from.startsWith(".")) continue;
      const path = resolve(root, dirname(source.file), from);
      const file = relative(root, path).split(sep).join("/");
      if (!file.startsWith("../") || path.split(sep).includes("node_modules") || !moduleFile.test(path)) continue;
      if (imported.some((s) => s.file === file) || !existsSync(path)) continue;
      const module = parsed(path, file);
      imported.push(module);
      visit(module);
    }
  };
  for (const source of sources) visit(source);
  return imported;
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

/** An import of one spec file from another that crosses into a service. */
interface ServiceImport {
  readonly source: SourceFile;
  readonly statement: Parsed["program"]["body"][number];
  /** The services that the importing file exports values of. */
  readonly within: readonly string[];
  /** A service that the imported file exports values of and the importing file exports none of. */
  readonly service: string;
  /** Whether every name that the import takes is a contract of that service. */
  readonly contract: boolean;
}

interface FileExport {
  readonly file: string;
  readonly name: string;
  readonly place: Place;
  readonly value: unknown;
}

/**
 * The imports across services. A file belongs to the services that its exported values belong to (definitions,
 * definers, contracts, scenarios, and constants); a file that exports none of them belongs to no service, and its
 * imports cross nothing. An import crosses into each service of the imported file that the importing file does not
 * belong to.
 */
function serviceImports(
  sources: readonly SourceFile[],
  exports: readonly FileExport[],
  serviceOf: (value: unknown) => string | undefined,
): ServiceImport[] {
  const servicesOf = (file: string) =>
    new Set(exports.flatMap((e) => (e.file === file ? (serviceOf(e.value) ?? []) : [])));
  const known = new Set(sources.map((s) => s.file));
  return sources.flatMap((source) => {
    const own = servicesOf(source.file);
    if (own.size === 0) return [];
    return source.program.body.flatMap((statement): ServiceImport[] => {
      if (statement.type !== "ImportDeclaration" || !statement.source.value.startsWith(".")) return [];
      const file = posix.normalize(posix.join(posix.dirname(source.file), statement.source.value));
      if (!known.has(file)) return [];
      const taken = statement.specifiers.map((s) =>
        s.type === "ImportSpecifier" && s.imported.type === "Identifier" ? s.imported.name : undefined,
      );
      const values = (name: string | undefined) =>
        exports.filter((e) => e.file === file && (name === undefined || e.name === name)).map((e) => e.value);
      return [...servicesOf(file)]
        .filter((service) => !own.has(service))
        .map((service) => ({
          source,
          statement,
          within: [...own],
          service,
          contract: taken.every((name) => values(name).every((v) => isContract(v) && serviceOf(v) === service)),
        }));
    });
  });
}

/** The spec in `root`, and what keeps the loader from reading it faithfully. */
export async function loadSpec(root: string): Promise<{ readonly spec: Spec; readonly malformed: Found<Malformed>[] }> {
  const found: Omit<Named<Definition>, "service">[] = [];
  const foundContracts: { readonly place: Place; readonly value: Readonly<Record<string, unknown>> }[] = [];
  const foundConstants: { readonly name: string; readonly place: Place; readonly value: unknown }[] = [];
  const foundScenarios: { readonly name: string; readonly place: Place; readonly value: ScenarioDefinition }[] = [];
  const sources: SourceFile[] = [];
  const definerExports: DefinerExport[] = [];
  const fileExports: FileExport[] = [];
  for (const path of tsFiles(root)) {
    const source = parsed(path, relative(root, path).split(sep).join("/"));
    const { file } = source;
    sources.push(source);
    const exports = exportsOf(source.program);
    const module: Record<string, unknown> = await import(pathToFileURL(path).href);
    // A module namespace object lists exports in name order; restore source order.
    const written = Object.entries(module).sort(([a], [b]) => (exports.get(a) ?? 0) - (exports.get(b) ?? 0));
    for (const [name, value] of written) {
      const place = placeIn(source, exports.get(name) ?? 0);
      fileExports.push({ file, name, place, value });
      const definer = definerService(value);
      if (isScenarioDefinition(value)) {
        if (!foundScenarios.some((s) => s.value === value)) foundScenarios.push({ name, place, value });
      } else if (isDefinition(value)) {
        if (!found.some((d) => d.definition === value)) found.push({ name, place, definition: value });
      } else if (definer !== undefined) definerExports.push({ definition: definer, place });
      else if (isContract(value)) foundContracts.push({ place, value });
      else if (constantsSchema(value) !== undefined && !foundConstants.some((c) => c.value === value))
        foundConstants.push({ name, place, value });
    }
  }
  const owned = owners(found, definerExports);
  const { services, definitions } = owned;
  const serviceNames = new Map([...services].map(([name, s]) => [s.definition, name]));
  const ownerName = (definer: ServiceDefinition | undefined) =>
    definer === undefined ? undefined : serviceNames.get(definer);
  const contracts = foundContracts.flatMap(({ place, value }): Contract[] => {
    const service = ownerName(contractService(value));
    return service === undefined ? [] : [{ service, place, members: value, value }];
  });
  const unknownServices: Found<Malformed>[] = [];
  const constants = foundConstants.flatMap(({ name, place, value }): Named<Constants>[] => {
    const service = constantsService(value) ?? "";
    const schema = constantsSchema(value);
    if (!services.has(service) || schema === undefined) {
      const violation: Malformed = { kind: "Malformed.unknownService", definition: null, data: { name: service } };
      unknownServices.push({ violation, place });
      return [];
    }
    return [{ name, service, place, definition: { schema, values: value as Constants["values"] } }];
  });
  const defined = foundScenarios.flatMap(({ name, place, value }): Named<ScenarioDefinition>[] => {
    const service = ownerName(scenarioService(value));
    return service === undefined ? [] : [{ name, service, place, definition: value }];
  });
  const definitionService = new Map<unknown, string>(definitions.map((d) => [d.definition, d.service]));
  const serviceOf = (value: unknown): string | undefined =>
    definitionService.get(value) ??
    ownerName(definerService(value)) ??
    ownerName(contractService(value)) ??
    ownerName(scenarioService(value)) ??
    constants.find((c) => c.definition.values === value)?.service;
  const namedExports = fileExports.flatMap(({ name, place, value }): NamedExport[] => {
    const service = serviceOf(value);
    const named = isDefinition(value) || isScenarioDefinition(value) || constantsSchema(value) !== undefined;
    return named && service !== undefined ? [{ name, service, place, value }] : [];
  });
  const names = new Map<unknown, Named<Definition>>(definitions.map((d) => [d.definition, d]));
  const built = structureOf(definitions, names, services, contracts);
  const opaque = opaqueCollections(definitions, constants);
  const exported = new Set(found.map((d) => d.definition));
  const loaded = loadScenarios(root, defined, services, (d) => {
    const n = names.get(d);
    return n === undefined ? undefined : { service: n.service, name: n.name };
  });
  const serviceNamed = [...services].map(([name, { place }]) => ({ name, place }));
  const spec: Spec = {
    root,
    definitions,
    contracts,
    constants,
    scenarios: loaded.scenarios,
    sources,
    imported: importedOutside(root, sources),
    imports: serviceImports(sources, fileExports, serviceOf),
    names,
    services,
    structure: built.structure,
  };
  const malformed = [
    ...duplicateNames(namedExports),
    ...owned.malformed,
    ...unknownServices,
    ...reservedNames([...serviceNamed, ...defined]),
    ...caseCollisions(serviceNamed),
    ...[...services.keys()].flatMap((service) => caseCollisions(defined.filter((s) => s.service === service))),
    ...unexportedDefinitions(definitions, services, contracts, constants, exported),
    ...opaque,
    ...unrepresentableSchemas(definitions, constants),
    ...misplacedSelfRefs(definitions, constants),
    ...defaultSchemas(definitions, built.structure, opaque, built.thrownDefaults),
    ...built.unresolvedReferences,
    ...loaded.malformed,
  ];
  if (malformed.length === 0 && built.unnamed.length > 0)
    throw new InternalError(`${built.unnamed.join(", ")} names a value that no export names, and no check reports it`);
  return { spec, malformed };
}

export function structured(spec: Pick<Spec, "definitions" | "structure">) {
  return spec.definitions.map((named, i) => ({
    named,
    structure: spec.structure.definitions[i] as DefinitionStructure,
  }));
}

export function charts(spec: Pick<Spec, "definitions" | "structure">) {
  return structured(spec).flatMap(({ named, structure }) => {
    const chart = chartOf(named.definition);
    return (structure.kind === "machine" || structure.kind === "screen") && chart !== undefined
      ? [{ named, chart, structure }]
      : [];
  });
}
