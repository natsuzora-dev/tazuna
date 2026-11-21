import type { z } from "zod";
import { partAt, writtenAs } from "../data/jsonSchema.ts";
import type { Malformed } from "../data/malformed.ts";
import type { Schema, SchemaStep } from "../data/schema.generated.ts";
import { schemaNode } from "../data/schemaNode.ts";
import { type Json, objectOf, type Shape } from "../data/values.ts";
import type { Definition, Named, Place } from "../dsl/definition.ts";
import { keyTarget } from "../dsl/entity.ts";
import type { Explore as Declared, Domain as DeclaredDomain } from "../dsl/explore.ts";
import type { Domain, Explore, Structure } from "../spec/structure.generated.ts";
import { schemaIn } from "../spec/structure.ts";
import type { Found } from "./found.ts";

const isJson = (value: unknown): value is Json =>
  value === null ||
  typeof value === "string" ||
  typeof value === "boolean" ||
  (typeof value === "number" && Number.isFinite(value)) ||
  (Array.isArray(value) && value.every(isJson)) ||
  (typeof value === "object" &&
    Object.getPrototypeOf(value) === Object.prototype &&
    Object.values(value as object).every(isJson));

/** A domain value that is not JSON or that its schema rejects, refinements included, is Malformed.domainValue. */
export function domainValues(service: string, declared: Declared, place: Place): Found<Malformed>[] {
  return declared.domains.flatMap((d, domain) =>
    d.values.flatMap((value, index): Found<Malformed>[] => {
      let accepted: boolean;
      try {
        accepted = isJson(value) && d.schema.safeParse(value).success;
      } catch {
        accepted = false;
      }
      return accepted
        ? []
        : [
            {
              violation: { kind: "Malformed.domainValue", definition: null, data: { service, domain, value: index } },
              place,
            },
          ];
    }),
  );
}

/**
 * The entity whose key the node that `schema` is written as holds, or undefined. A nullable node is a union that holds
 * the key in one option and null in the other, and the key option is the node that a key domain names.
 */
function keyAt(schema: z.ZodType): unknown {
  const written = writtenAs(schema);
  if (schemaNode(written.at(-1) ?? schema).type === "nullable") return undefined;
  return written.map(keyTarget).find((target) => target !== undefined);
}

/** Whether `d` names the node whose Zod part is `part`: the schema written there, or a key of the same entity. */
function names(d: DeclaredDomain, part: z.ZodType): boolean {
  const target = keyAt(d.schema);
  return writtenAs(part).includes(d.schema) || (target !== undefined && keyAt(part) === target);
}

const isObject = (v: Json | undefined): v is { readonly [key: string]: Json } =>
  typeof v === "object" && v !== null && !Array.isArray(v);

/**
 * The domains of `declared` at the nodes of the JSON Schema `json` of `schema`, whose Zod schema is `root`: each node
 * that treeOf reads, the first domain that names it, and no node below it.
 */
function domainsIn(declared: Declared, schema: Schema, json: Json, root: z.ZodType): Domain[] {
  const found: Domain[] = [];
  const walk = (s: Json, path: readonly SchemaStep[], part: z.ZodType): void => {
    const d = declared.domains.find((x) => names(x, part));
    if (d !== undefined) {
      found.push({ schema, path, values: d.values as Json[] });
      return;
    }
    if (!isObject(s)) return;
    const into = (child: Json, step: SchemaStep) => walk(child, [...path, step], partAt(part, [step]));
    const options = Array.isArray(s["anyOf"]) ? s["anyOf"] : Array.isArray(s["oneOf"]) ? s["oneOf"] : undefined;
    if (options !== undefined) {
      for (const [index, o] of options.entries()) into(o, { kind: "option", index });
      return;
    }
    const type = s["type"];
    // Zod writes a nullable of a plain type as a type list, and any other type list once per type of one schema.
    if (Array.isArray(type)) {
      const nullable = schemaNode(writtenAs(part).at(-1) ?? part).type === "nullable";
      for (const [index, t] of type.entries()) {
        const step: SchemaStep = { kind: "option", index };
        walk({ ...s, type: t }, [...path, step], nullable ? partAt(part, [step]) : part);
      }
      return;
    }
    const properties = s["properties"];
    if (type === "object" && isObject(properties))
      for (const [name, p] of Object.entries(properties)) into(p, { kind: "field", name });
  };
  walk(json, [], root);
  return found;
}

/** The shape of each schema that a move may carry: an input, an output, an event payload, or a control payload. */
function shapes(definitions: readonly Named<Definition>[]): [Schema, Shape][] {
  return definitions.flatMap(({ service, name, definition: d }): [Schema, Shape][] => {
    const ref = { service, name };
    switch (d.kind) {
      case "command":
      case "query":
        return [
          [{ kind: "input", definition: ref }, d.input],
          ...(d.output === undefined ? [] : [[{ kind: "output", definition: ref }, d.output] as [Schema, Shape]]),
        ];
      case "event":
        return [[{ kind: "payload", event: ref }, d.payload]];
      case "screen":
        return Object.entries(d.controls as Readonly<Record<string, { readonly payload?: Shape }>>).flatMap(
          ([control, c]): [Schema, Shape][] =>
            c.payload === undefined ? [] : [[{ kind: "control", screen: ref, control }, c.payload]],
        );
      default:
        return [];
    }
  });
}

/** The explore of `service`, with each domain at the nodes that it names (Structure.explores). */
export function exploreOf(
  structure: Pick<Structure, "definitions">,
  definitions: readonly Named<Definition>[],
  service: string,
  declared: Declared,
): Explore {
  const domains = shapes(definitions).flatMap(([schema, shape]) => {
    const json = schemaIn(structure, schema);
    return json === undefined ? [] : domainsIn(declared, schema, json, objectOf(shape));
  });
  return { service, depth: declared.depth, domains };
}
