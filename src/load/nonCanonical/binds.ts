import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { AnyCommand, Automation } from "../../dsl/definition.ts";
import type { Found } from "../found.ts";
import { placeIn, type Spec } from "../load.ts";

interface Node {
  readonly type?: string;
  readonly start?: number;
  readonly name?: string;
  readonly computed?: boolean;
  readonly key?: Node;
  readonly value?: Node;
  readonly object?: Node;
  readonly property?: Node;
  readonly properties?: readonly Node[];
  readonly arguments?: readonly Node[];
  readonly id?: Node;
  readonly init?: Node;
  readonly declarations?: readonly Node[];
  readonly declaration?: Node;
}

const isBound = (n: Node | undefined) => n?.type === "Identifier" && n.name === "bound";

function boundReads(init: Node): Set<string> | "all" {
  const reads = new Set<string>();
  let all = false;
  const visit = (node: unknown): void => {
    if (node === null || typeof node !== "object") return;
    if (Array.isArray(node)) {
      for (const child of node) visit(child);
      return;
    }
    const n = node as Node;
    if (n.type === "MemberExpression" && !n.computed && isBound(n.object) && n.property?.name)
      reads.add(n.property.name);
    if (n.type === "Property" && n.key?.name === "bound" && n.value?.type === "ObjectPattern")
      for (const p of n.value.properties ?? []) if (p.key?.name) reads.add(p.key.name);
    if (n.type === "CallExpression" && (n.arguments ?? []).some(isBound)) all = true;
    for (const value of Object.values(n)) visit(value);
  };
  visit(init);
  return all ? "all" : reads;
}

export const check = (spec: Spec): Found<NonCanonical>[] =>
  spec.definitions.flatMap((d) => {
    if (d.definition.kind !== "automation" && d.definition.kind !== "command") return [];
    const names = Object.keys((d.definition as Automation | AnyCommand).binds);
    const source = spec.sources.find((s) => s.file === d.place.file);
    if (names.length === 0 || source === undefined) return [];
    const declarations = (source.program.body as unknown as Node[]).flatMap(
      (s) => (s.type === "ExportNamedDeclaration" ? s.declaration : s)?.declarations ?? [],
    );
    const init = declarations.find((v) => v.id?.name === d.name)?.init;
    if (init === undefined) return [];
    const reads = boundReads(init);
    if (reads === "all") return [];
    const definition = { service: d.service, name: d.name };
    return names
      .filter((name) => !reads.has(name))
      .map((binding) => ({
        violation: { kind: "NonCanonical.unreadBinding", definition, data: { binding } },
        place: placeIn(source, init.start ?? 0),
      }));
  });
