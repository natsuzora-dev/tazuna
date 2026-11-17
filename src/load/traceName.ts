import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Definition } from "../dsl/definition.ts";
import { traceNameOfRef } from "../spec/structure.ts";
import type { Spec } from "./load.ts";

export function refOfDefinition(spec: Spec, definition: unknown): DefinitionRef {
  const named = spec.names.get(definition);
  if (named === undefined) throw new Error("the value is no named definition of the spec");
  return { service: named.service, name: named.name };
}

/** Returns traceNameOfRef of the definition `d`, or `?` when `d` is not a named definition. */
export function traceName(spec: Spec, d: unknown, from?: string): string {
  const named = spec.names.get(d);
  return named === undefined ? "?" : traceNameOfRef(named, from);
}

export function definitionOfTraceName<K extends Definition["kind"]>(
  spec: Spec,
  service: string,
  name: string | undefined,
  ...kinds: readonly K[]
): Extract<Definition, { readonly kind: K }> | undefined {
  if (name === undefined) return undefined;
  return spec.definitions.find(
    (d) => (kinds as readonly string[]).includes(d.definition.kind) && traceName(spec, d.definition, service) === name,
  )?.definition as Extract<Definition, { readonly kind: K }> | undefined;
}
