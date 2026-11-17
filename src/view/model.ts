import { existsSync } from "node:fs";
import { z } from "zod";
import type { CheckedSpec } from "../check/spec.ts";
import { type JsonSchema, jsonSchema } from "../data/jsonSchema.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import type { MalformedLine } from "../data/trace.ts";
import { parseSnapshotFile, snapshotPath } from "../data/traceFile.ts";
import type { TransitionRef } from "../data/transitionRef.ts";
import type { Json, Shape } from "../data/values.ts";
import type { Named } from "../dsl/definition.ts";
import { type AnyEntity, refTarget } from "../dsl/entity.ts";
import { type Spec, structured } from "../load/load.ts";
import {
  type ActivityStructure,
  type ChartStructure,
  type DefinitionStructure,
  isAnswerTransition,
  type StateStructure,
  stateNamed,
  type TransitionStructure,
  transitionRef,
} from "../spec/structure.ts";
import type {
  ActivityView,
  DefinitionView,
  EntityView,
  FieldView,
  FlowEntry,
  ScenarioView,
  ServiceView,
  StateView,
  TransitionView,
  Trigger,
  ViewModel,
} from "./types.ts";

function schemaOf(schema: z.ZodType): JsonSchema {
  const { $schema: _, ...converted } = jsonSchema(schema);
  return converted;
}

function toJson(spec: Spec, value: unknown): Json {
  if (value === null || typeof value === "boolean" || typeof value === "number" || typeof value === "string")
    return value;
  if (value === undefined) return null;
  if (typeof value === "function") return value.toString();
  if (value instanceof z.ZodType) return schemaOf(value) as Json;
  const named = spec.names.get(value);
  if (named !== undefined) return { kind: named.definition.kind, service: named.service, name: named.name };
  const service = [...spec.services].find(([, s]) => s.definition === value);
  if (service !== undefined) return service[0];
  if (Array.isArray(value)) return value.map((v) => toJson(spec, v));
  return fieldsJson(spec, value as object);
}

/** Returns the JSON of each field of `value`, unlike toJson, which turns a definition into a reference. */
const fieldsJson = (spec: Spec, value: object): Json =>
  Object.fromEntries(Object.entries(value).map(([k, v]) => [k, toJson(spec, v)]));

const activityKind = (keyword: string): ActivityView["kind"] =>
  keyword === "opens" ? "screen" : keyword === "sends" ? "command" : "query";

const activityView = (a: ActivityStructure): ActivityView => ({ ...a, kind: activityKind(a.keyword) });

function trigger(chart: ChartStructure, t: TransitionStructure): Trigger {
  const [keyword = "", name = "", answer = ""] = t.keys;
  if (isAnswerTransition(t)) return { type: "answer", keyword, name, answer, kind: activityKind(keyword) };
  if (keyword === "on") return { type: Object.hasOwn(chart.controls, name) ? "control" : "event", name };
  if (keyword === "after") return { type: "after", deadline: name };
  if (keyword === "always") return { type: "always" };
  return { type: "onDone" };
}

function transitionId({ state, keys, index }: TransitionRef): string {
  return `${keys.join(".")}[${index}] in ${state ?? "root"}`;
}

function chartView(name: string, chart: ChartStructure): StateView {
  const transitionView = (t: TransitionStructure): TransitionView => ({
    ...t,
    id: transitionId(transitionRef(t)),
    trigger: trigger(chart, t),
  });
  const tree = ({ children, activities, transitions, ...state }: StateStructure): StateView => ({
    ...state,
    activities: activities.map(activityView),
    transitions: transitions.map(transitionView),
    states: children.map((child) => tree(stateNamed(chart, child) as StateStructure)),
  });
  return tree({
    name,
    path: [],
    parent: null,
    kind: "compound",
    initial: chart.initial,
    children: chart.states.filter((s) => s.parent === null).map((s) => s.name),
    offers: chart.offers,
    activities: [],
    transitions: chart.on,
    deadlines: [],
  });
}

type EntityStructure = Extract<DefinitionStructure, { kind: "entity" }>;

const withoutNull = (schema: JsonSchema): JsonSchema => {
  const options = ((schema["anyOf"] as JsonSchema[] | undefined) ?? []).filter((o) => o["type"] !== "null");
  if (options.length === 1) return options[0] as JsonSchema;
  const type = schema["type"];
  if (Array.isArray(type)) return { ...schema, type: type.filter((t) => t !== "null") };
  return schema;
};

function typeText(schema: JsonSchema): string {
  const s = withoutNull(schema);
  const type = Array.isArray(s["type"]) ? (s["type"] as string[]).join(" | ") : s["type"];
  if (typeof s["format"] === "string") return s["format"] === "date-time" ? "datetime" : s["format"];
  if (s["enum"] !== undefined) return "enum";
  if (s["anyOf"] !== undefined || s["oneOf"] !== undefined) return "union";
  if (type === "integer") return "int";
  if (type === "array") return `${typeText((s["items"] as JsonSchema | undefined) ?? {})}[]`;
  return typeof type === "string" ? type : "any";
}

function entityView(spec: Spec, entity: AnyEntity, structure: EntityStructure): EntityView {
  return {
    key: structure.key,
    unique: structure.unique,
    invariants: Object.keys(entity.invariants),
    fields: Object.entries(entity.fields as Shape).map(([name, field]): FieldView => {
      const schema = schemaOf(field);
      const target = refTarget(field);
      const named = target === undefined ? undefined : spec.names.get(target);
      return {
        name,
        type: typeText(schema),
        nullable: field.safeParse(null).success,
        description: typeof schema["description"] === "string" ? schema["description"] : null,
        ref: named === undefined ? null : { service: named.service, name: named.name },
      };
    }),
  };
}

/** The service that sent the message with id `id` in a simulation, which names it `<sender>/<id>` (Sim.receivedId). */
function senderOf(id: string): string | undefined {
  const parts = id.split("/");
  return parts.length === 2 ? parts[0] : undefined;
}

/**
 * Returns the lifelines and messages of a trace. A message from another service of the simulation comes from its
 * sender's lifeline, and any other `in` line from the scenario lifeline; a request goes to the service that its name
 * starts with, and an answer or a subscription end goes back between the request's two lifelines.
 */
function flow(service: string, trace: readonly TraceLine[]): Pick<ScenarioView, "lifelines" | "entries"> {
  const lifelines = [service];
  const targets = new Map<string, string>();
  const targetOf = (id: string) => targets.get(id) ?? null;
  const between = (other: string | null, dir: TraceLine["dir"]) =>
    dir === "in" ? { from: other, to: service } : { from: service, to: other };
  const entries = trace.flatMap((l, line): FlowEntry[] => {
    if (l.type === "time") return [{ type: "time", line }];
    if (l.dir === "in") {
      const sender = l.type === "answer" ? (targetOf(l.to) ?? senderOf(l.id) ?? null) : (senderOf(l.id) ?? null);
      if (sender !== null && !lifelines.includes(sender)) lifelines.push(sender);
      return [{ type: "message", line, ...between(sender, "in") }];
    }
    if (l.type === "event") return [{ type: "message", line, from: service, to: service }];
    if (l.type === "answer") return [{ type: "message", line, from: service, to: null }];
    if (l.type === "unsubscribe") return [{ type: "message", line, from: service, to: targetOf(l.to) }];
    const [owner] = l.name.split(".");
    if (owner === undefined || owner === l.name) return [{ type: "message", line, from: service, to: null }];
    if (!lifelines.includes(owner)) lifelines.push(owner);
    targets.set(l.id, owner);
    return [{ type: "message", line, from: service, to: owner }];
  });
  return { lifelines, entries };
}

function snapshot(path: string): { readonly trace: TraceLine[] | null; readonly error: MalformedLine | null } {
  if (!existsSync(path)) return { trace: null, error: null };
  const { lines, malformed } = parseSnapshotFile(path);
  const [first] = malformed;
  return first === undefined ? { trace: lines, error: null } : { trace: null, error: first };
}

function scenarioView(spec: Spec, scenario: Named<{ readonly description: string }>): ScenarioView {
  const shot = snapshot(snapshotPath(spec, scenario));
  return {
    service: scenario.service,
    name: scenario.name,
    description: scenario.definition.description,
    ...shot,
    ...flow(scenario.service, shot.trace ?? []),
  };
}

export function viewModel(spec: CheckedSpec, path: string): ViewModel {
  // A scenario file imports the contracts of the peers that its Given lists, which the service itself does not use.
  const scenarioFiles = new Set(spec.scenarios.map((s) => s.place.file));
  const imports = spec.imports.filter((i) => i.contract && !scenarioFiles.has(i.source.file));
  const services = [...spec.services].map(([name, owner]): ServiceView => {
    const definitions = structured(spec)
      .filter(({ named }) => named.service === name)
      .map(
        ({ named: d, structure }): DefinitionView => ({
          kind: structure.kind,
          name: d.name,
          definition: fieldsJson(spec, d.definition),
          chart: structure.kind === "machine" || structure.kind === "screen" ? chartView(d.name, structure) : null,
          entity: structure.kind === "entity" ? entityView(spec, d.definition as AnyEntity, structure) : null,
        }),
      );
    return {
      kind: owner.definition.external
        ? "external"
        : definitions.some((d) => d.kind === "screen")
          ? "screens"
          : "service",
      name,
      description: owner.definition.description,
      uses: [...new Set(imports.filter((i) => i.within.includes(name)).map((i) => i.service))].sort(),
      invariants: fieldsJson(spec, owner.definition.invariants),
      definitions,
    };
  });
  return {
    spec: path,
    services,
    scenarios: spec.scenarios.map((s) => scenarioView(spec, s)),
  };
}
