import {
  cryptoModules,
  localeMethods,
  memberObjects,
  nondeterministicGlobals,
  nondeterministicMembers,
  type Restricted,
  suppressionMarks,
} from "../../data/restricted.ts";
import type { Found } from "../../load/found.ts";
import { placeIn, type SourceFile, type Spec } from "../../load/load.ts";

interface Node {
  readonly type?: string;
  readonly start?: number;
  readonly end?: number;
  readonly name?: string;
  readonly computed?: boolean;
  readonly value?: unknown;
  readonly object?: Node;
  readonly property?: Node;
  readonly key?: Node;
  readonly source?: Node;
  readonly id?: Node & { readonly properties?: readonly Node[] };
  readonly init?: Node;
  readonly typeAnnotation?: {
    readonly start: number;
    readonly end: number;
    readonly typeName?: { readonly name?: string };
  };
}

const isOneOf = <T extends string>(list: readonly T[], value: unknown): value is T => list.includes(value as T);

const typeKeys = new Set(["typeAnnotation", "typeArguments", "typeParameters", "returnType", "superTypeArguments"]);
const bindingKeys = new Set(["id", "params", "local", "imported", "exported", "label"]);

const propertyName = (n: Node, computed: boolean | undefined): string | undefined =>
  computed ? (typeof n.value === "string" ? n.value : undefined) : n.name;

const memberRead = (object: Node | undefined, property: string | undefined) =>
  nondeterministicMembers.find(
    (m) => object?.type === "Identifier" && object.name === m.object && property === m.property,
  );

function imports(spec: Spec): Found<Restricted>[] {
  return spec.imports
    .filter((i) => !i.contract)
    .map(({ source, statement, service }) => ({
      violation: { kind: "Restricted.crossServiceImport", definition: null, data: { service } },
      place: placeIn(source, statement.start),
    }));
}

function nondeterminism(source: SourceFile): Found<Restricted>[] {
  const found: Found<Restricted>[] = [];
  const report = (n: Node, violation: Restricted) => found.push({ violation, place: placeIn(source, n.start ?? 0) });
  const visit = (node: unknown, parent: Node | undefined, key: string): void => {
    if (node === null || typeof node !== "object") return;
    if (Array.isArray(node)) {
      for (const child of node) visit(child, parent, key);
      return;
    }
    const n = node as Node;
    const property = parent?.type === "MemberExpression" && key === "property" && !parent.computed;
    const propertyKey = parent?.type === "Property" && key === "key" && !parent.computed;
    const named = !property && !propertyKey && !bindingKeys.has(key);
    if (n.type === "Identifier" && isOneOf(nondeterministicGlobals, n.name) && named)
      report(n, { kind: "Restricted.global", definition: null, data: { global: n.name } });
    if (n.type === "Identifier" && isOneOf(memberObjects, n.name) && named) {
      const object = parent?.type === "MemberExpression" && key === "object";
      const destructured =
        parent?.type === "VariableDeclarator" && key === "init" && parent.id?.type === "ObjectPattern";
      if (!object && !destructured) report(n, { kind: "Restricted.alias", definition: null, data: { object: n.name } });
    }
    const name = n.type === "MemberExpression" && n.property ? propertyName(n.property, n.computed) : undefined;
    const read = name === undefined ? undefined : memberRead(n.object, name);
    if (read !== undefined) report(n, { kind: "Restricted.member", definition: null, data: { ...read } });
    if (isOneOf(localeMethods, name))
      report(n, { kind: "Restricted.localeMethod", definition: null, data: { method: name } });
    if (n.type === "VariableDeclarator" && n.id?.type === "ObjectPattern")
      for (const p of n.id.properties ?? []) {
        const destructured = p.key ? memberRead(n.init, propertyName(p.key, p.computed)) : undefined;
        if (destructured !== undefined)
          report(p, { kind: "Restricted.member", definition: null, data: { ...destructured } });
      }
    if ((n.type === "ImportDeclaration" || n.type === "ImportExpression") && isOneOf(cryptoModules, n.source?.value))
      report(n, { kind: "Restricted.cryptoImport", definition: null, data: { module: n.source.value } });
    for (const [k, value] of Object.entries(node)) if (!typeKeys.has(k)) visit(value, n, k);
  };
  visit(source.program, undefined, "");
  return found;
}

/**
 * Reports each `let` or `var` at the top of a module, whose value a spec function could read after another wrote it.
 */
function moduleState(source: SourceFile): Found<Restricted>[] {
  return source.program.body.flatMap((statement) => {
    const declaration = statement.type === "ExportNamedDeclaration" ? statement.declaration : statement;
    return declaration?.type === "VariableDeclaration" && (declaration.kind === "let" || declaration.kind === "var")
      ? [
          {
            violation: { kind: "Restricted.mutableModule", definition: null, data: { declaration: declaration.kind } },
            place: placeIn(source, statement.start ?? 0),
          },
        ]
      : [];
  });
}

/** tsc's patterns for a comment that suppresses errors: a line comment, or the last line of a block comment. */
const tsDirectives = {
  Line: /^\/\/\/?\s*@(ts-expect-error|ts-ignore)/,
  Block: /^(?:\/|\*)*\s*@(ts-expect-error|ts-ignore)/,
} as const;

const tsMarks: readonly string[] = ["@ts-ignore", "@ts-expect-error"];

/** The suppression mark of the comment, where the two marks of tsc count as tsc reads them. */
function suppressionMark(
  text: string,
  type: keyof typeof tsDirectives,
  value: string,
): (typeof suppressionMarks)[number] | undefined {
  const lastLine = type === "Line" ? text : (text.split(/[\n\r\u2028\u2029]/).at(-1) ?? "");
  const directive = tsDirectives[type].exec(lastLine.trimStart())?.[1];
  return directive === undefined
    ? suppressionMarks.find((s) => !tsMarks.includes(s) && value.trimStart().startsWith(s))
    : suppressionMarks.find((s) => s === `@${directive}`);
}

function assertions(source: SourceFile): Found<Restricted>[] {
  const found: Found<Restricted>[] = [];
  const report = (start: number, violation: Restricted) => found.push({ violation, place: placeIn(source, start) });
  const visit = (node: unknown): void => {
    if (node === null || typeof node !== "object") return;
    if (Array.isArray(node)) {
      for (const child of node) visit(child);
      return;
    }
    const n = node as Node;
    if (n.type === "TSNonNullExpression")
      report(n.start ?? 0, { kind: "Restricted.nonNull", definition: null, data: {} });
    if (n.type === "TSAnyKeyword") report(n.start ?? 0, { kind: "Restricted.any", definition: null, data: {} });
    if (n.type === "TSAsExpression" && n.typeAnnotation !== undefined && n.typeAnnotation.typeName?.name !== "const") {
      const type = source.text.slice(n.typeAnnotation.start, n.typeAnnotation.end);
      report(n.start ?? 0, { kind: "Restricted.as", definition: null, data: { type } });
    }
    for (const value of Object.values(node)) visit(value);
  };
  visit(source.program);
  for (const comment of source.comments) {
    const mark = suppressionMark(source.text.slice(comment.start, comment.end), comment.type, comment.value);
    if (mark !== undefined) report(comment.start, { kind: "Restricted.suppression", definition: null, data: { mark } });
  }
  return found;
}

export function check(spec: Spec): Found<Restricted>[] {
  const files = [...spec.sources, ...spec.imported];
  return [
    ...imports(spec),
    ...files.flatMap(nondeterminism),
    ...files.flatMap(moduleState),
    ...files.flatMap(assertions),
  ];
}
