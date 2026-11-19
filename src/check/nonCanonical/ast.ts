import type { Argument, Expression, Node, ObjectProperty, PropertyKey, VariableDeclarator } from "oxc-parser";
import type { Definition, Named, Place } from "../../dsl/definition.ts";
import { placeIn, type SourceFile, type Spec } from "../../load/load.ts";

/** `node` without the parentheses, `as`, and `satisfies` around it, which change no value. */
export function unwrap(node: Expression): Expression {
  let e = node;
  while (e.type === "ParenthesizedExpression" || e.type === "TSAsExpression" || e.type === "TSSatisfiesExpression")
    e = e.expression;
  return e;
}

/** The name of the key of `p`, written as an identifier or a string. */
export function keyName(p: { readonly computed: boolean; readonly key: PropertyKey }): string | undefined {
  if (p.computed) return undefined;
  if (p.key.type === "Identifier") return p.key.name;
  return p.key.type === "Literal" && typeof p.key.value === "string" ? p.key.value : undefined;
}

/** The properties of `node` with a written key, if it is an object literal. */
export const propertiesOf = (node: Expression): [string, ObjectProperty][] => {
  const e = unwrap(node);
  return e.type !== "ObjectExpression"
    ? []
    : e.properties.flatMap((p): [string, ObjectProperty][] => {
        const key = p.type === "Property" ? keyName(p) : undefined;
        return p.type === "Property" && key !== undefined ? [[key, p]] : [];
      });
};

/** The value of the property `key` of `node`, if it is an object literal that writes one. */
export const property = (node: Expression, key: string): Expression | undefined =>
  propertiesOf(node).find(([k]) => k === key)?.[1].value;

/** Calls `f` on every node within `node`. */
export function visit(node: unknown, f: (node: Node) => void): void {
  if (node === null || typeof node !== "object") return;
  if (Array.isArray(node)) {
    for (const child of node) visit(child, f);
    return;
  }
  if ("type" in node) f(node as Node);
  for (const [key, value] of Object.entries(node)) if (key !== "parent") visit(value, f);
}

/** A call that made a definition or a service: the definer's call, or a method's on its result, such as `chart()`. */
interface Call {
  /** The method's name, or null for the definer's call. */
  readonly method: string | null;
  readonly arguments: readonly Argument[];
}

/** How a definition or a service was written: the calls that made it, the definer's first. */
export interface Written {
  readonly source: SourceFile;
  /** The definition, or null for a service. */
  readonly definition: Named<Definition> | null;
  readonly service: string;
  /** The expression that the declaration exports. */
  readonly init: Expression;
  readonly calls: readonly Call[];
}

function callsOf(init: Expression): Call[] {
  const calls: Call[] = [];
  let e = unwrap(init);
  while (e.type === "CallExpression") {
    const callee = unwrap(e.callee);
    const method = callee.type === "MemberExpression" && !callee.computed ? callee.property.name : null;
    calls.unshift({ method, arguments: e.arguments });
    e = callee.type === "MemberExpression" ? unwrap(callee.object) : callee;
  }
  return calls.length === 0 ? [] : [{ ...(calls[0] as Call), method: null }, ...calls.slice(1)];
}

const samePlace = (a: Place, b: Place) => a.file === b.file && a.line === b.line && a.column === b.column;

/** The places of the names that `declarator` exports. */
function placesOf(source: SourceFile, declarator: VariableDeclarator): Place[] {
  const { id } = declarator;
  if (id.type === "Identifier") return [placeIn(source, id.start)];
  if (id.type !== "ObjectPattern") return [];
  return id.properties.flatMap((p) =>
    p.type === "Property" && p.value.type === "Identifier" ? [placeIn(source, p.value.start)] : [],
  );
}

/**
 * How each definition and service of `spec` was written in its exported declaration. Scenarios and constants are left
 * out: they write data, not keywords.
 */
export const writtenOf = (spec: Spec): Written[] =>
  spec.sources.flatMap((source) =>
    source.program.body.flatMap((statement) => {
      if (statement.type !== "ExportNamedDeclaration" || statement.declaration?.type !== "VariableDeclaration")
        return [];
      return statement.declaration.declarations.flatMap((declarator): Written[] => {
        if (declarator.init === null) return [];
        const places = placesOf(source, declarator);
        const at = (place: Place) => places.some((p) => samePlace(p, place));
        const definition = spec.definitions.find((d) => at(d.place));
        const service = [...spec.services].find(([, s]) => at(s.place))?.[0];
        const { init } = declarator;
        const calls = callsOf(init);
        if (definition !== undefined) return [{ source, definition, service: definition.service, init, calls }];
        return service === undefined ? [] : [{ source, definition: null, service, init, calls }];
      });
    }),
  );
