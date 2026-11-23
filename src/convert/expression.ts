import {
  type ArrowFunction,
  type BindingName,
  type CallExpression,
  type Expression,
  type FunctionDeclaration,
  type FunctionExpression,
  type Identifier,
  isArrayLiteralExpression,
  isArrowFunction,
  isAsExpression,
  isBinaryExpression,
  isBindingElement,
  isBlock,
  isCallExpression,
  isConditionalExpression,
  isFunctionDeclaration,
  isFunctionExpression,
  isIdentifier,
  isIfStatement,
  isNonNullExpression,
  isNoSubstitutionTemplateLiteral,
  isNumericLiteral,
  isObjectBindingPattern,
  isObjectLiteralExpression,
  isParenthesizedExpression,
  isPrefixUnaryExpression,
  isPropertyAccessExpression,
  isPropertyAssignment,
  isReturnStatement,
  isSatisfiesExpression,
  isShorthandPropertyAssignment,
  isSpreadElement,
  isStringLiteral,
  isTemplateExpression,
  isVariableDeclaration,
  isVariableDeclarationList,
  isVariableStatement,
  type Node,
  NodeFlags,
  type ObjectLiteralElementLike,
  type PropertyAccessExpression,
  type Statement,
  SyntaxKind,
} from "typescript/unstable/ast";
import { SignatureKind, SymbolFlags, type Type, TypeFlags, type TypeReference } from "typescript/unstable/sync";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { parseInstant } from "../data/time.ts";
import type { Json } from "../data/values.ts";
import type { Expr, Field } from "../spec/ir.generated.ts";
import type { Source, SpecFunctionNode } from "./sources.ts";

/**
 * An argument of a spec function: one that the IR names, `records`, which only the record operations read, or
 * `createKey`, which only a call reads.
 */
export type Arg = Extract<Expr, { readonly op: "arg" }>["arg"] | "records" | "createKey" | "refs";
type Special = "records" | "createKey";
type Relation = Extract<Expr, { readonly op: "compare" }>["relation"];

/** What the converter tells apart in a TS type: a member of a union, by how the IR reads its JSON. */
type Kind =
  | "string"
  | "number"
  | "boolean"
  | "null"
  | "undefined"
  | "date"
  | "array"
  /** An array with no element type, such as `[]`, which reads as a Bag does in a union with one. */
  | "empty"
  | "bag"
  | "table"
  | "emit"
  | "object"
  | "other";

const scalars: ReadonlySet<Kind> = new Set(["string", "number", "boolean", "null", "undefined"]);

/** A construct outside the IR, with the source text it is in. */
class Unconverted extends Error {}

/**
 * The names that a function body can read: a variable, the records argument, createKey, or the arguments object of a
 * function that takes it whole, whose fields read as the arguments do.
 */
type Scope = ReadonlyMap<string, "variable" | Special | "args">;

/** What the spec defines outside its functions, each by the file and name of the const that holds it. */
export interface Defined {
  /** The values of `constants()` groups, encoded. */
  readonly constants: ReadonlyMap<string, Readonly<Record<string, Json>>>;
  /** The names of entities. */
  readonly entities: ReadonlyMap<string, string>;
}

export const definedKey = (file: string, name: string): string => `${file}#${name}`;

/** Whether `file` is tazuna's module `module`, such as `dsl/service`, as source or as declarations. */
const isTazunaModule = (file: string, module: string): boolean =>
  new RegExp(`[/\\\\](src|dist)[/\\\\]${module.replace("/", "[/\\\\]")}\\.(d\\.)?ts$`).test(file);

type Helper = ArrowFunction | FunctionExpression | FunctionDeclaration;

const declared = (scope: Scope, name: string): Scope => new Map([...scope, [name, "variable"]]);

const arithmetic: ReadonlyMap<SyntaxKind, Extract<Expr, { readonly op: "arith" }>["operation"]> = new Map([
  [SyntaxKind.PlusToken, "add"],
  [SyntaxKind.MinusToken, "sub"],
  [SyntaxKind.AsteriskToken, "mul"],
]);

const relations: ReadonlyMap<SyntaxKind, Relation> = new Map([
  [SyntaxKind.LessThanToken, "lt"],
  [SyntaxKind.LessThanEqualsToken, "le"],
  [SyntaxKind.GreaterThanToken, "gt"],
  [SyntaxKind.GreaterThanEqualsToken, "ge"],
  [SyntaxKind.EqualsEqualsEqualsToken, "eq"],
]);

const stringSearches = { startsWith: "startsWith", endsWith: "endsWith", includes: "strIncludes" } as const;

const unwrapped = (node: Expression): Expression =>
  isParenthesizedExpression(node) || isNonNullExpression(node) || isAsExpression(node) || isSatisfiesExpression(node)
    ? unwrapped(node.expression)
    : node;

/** The nodes of `root` that hold `node`, outermost first, `node` excluded. */
function ancestorsOf(root: Node, node: Node): Node[] {
  const path: Node[] = [];
  const visit = (n: Node): void => {
    if (n === node || node.pos < n.pos || n.end < node.end) return;
    path.push(n);
    n.forEachChild(visit);
  };
  visit(root);
  return path;
}

/** Converts one spec function by its syntax and the checker's types. */
class Conversion {
  private readonly source: Source;
  /** The events that a decide's command lists, in the order of its `emits`. */
  private readonly events: readonly DefinitionRef[];
  private readonly defined: Defined;
  /** The entity of each top-level ref field of the input, whose record `refs` holds under the field's name. */
  private readonly refs: ReadonlyMap<string, string>;
  /** The argument that a name of the arguments object reads, once convertFunction knows the arguments. */
  private argument: (node: Node, name: string) => Expr = (node) => this.fail(node, "reads its arguments");
  /** The special arguments that the function receives. */
  private specials: ReadonlySet<Special> = new Set();
  /** How many callbacks of a collection method hold the expression being converted. */
  private callbacks = 0;
  /** The helpers being inlined, innermost last, so that a recursive one stays TS. */
  private readonly inlining: Helper[] = [];
  private fresh = 0;

  constructor(source: Source, events: readonly DefinitionRef[], defined: Defined, refs: ReadonlyMap<string, string>) {
    this.source = source;
    this.events = events;
    this.defined = defined;
    this.refs = refs;
  }

  /** The texts of the `emits` of `command({ emits }).decide(f)`, where `f` is the function converted. */
  private emitsTexts(): readonly string[] {
    const decide = ancestorsOf(this.source.file, this.source.node)
      .filter(isCallExpression)
      .findLast((c) => {
        const callee = unwrapped(c.expression);
        return isPropertyAccessExpression(callee) && isIdentifier(callee.name) && callee.name.text === "decide";
      });
    const callee = decide === undefined ? undefined : unwrapped(decide.expression);
    const command =
      callee !== undefined && isPropertyAccessExpression(callee) ? unwrapped(callee.expression) : undefined;
    const [definition] = command !== undefined && isCallExpression(command) ? command.arguments : [];
    if (definition === undefined || !isObjectLiteralExpression(definition)) return [];
    const emits = definition.properties.find(
      (p) => isPropertyAssignment(p) && isIdentifier(p.name) && p.name.text === "emits",
    );
    if (emits === undefined || !isPropertyAssignment(emits) || !isArrayLiteralExpression(emits.initializer)) return [];
    return emits.initializer.elements.map((e) => this.text(e));
  }

  private emitted(e: CallExpression, scope: Scope): Expr {
    const [event, payload, ...rest] = e.arguments;
    if (event === undefined || payload === undefined || rest.length > 0)
      this.fail(e, "emits with other than two arguments");
    const ref = this.events[this.emitsTexts().indexOf(this.text(event))];
    if (ref === undefined) this.fail(e, "emits an event that its command's emits does not name as written");
    return { op: "emit", event: ref, payload: this.expression(payload, scope) };
  }

  private text(node: Node): string {
    return node.getSourceFile().text.slice(node.pos, node.end).trim();
  }

  private fail(node: Node, reason: string): never {
    throw new Unconverted(`${reason}: ${this.text(node)}`);
  }

  private kinds(node: Node): ReadonlySet<Kind> {
    const type = this.source.checker.getTypeAtLocation(node);
    if (type === undefined) return new Set(["other"]);
    const members = type.isUnionType() ? type.getTypes() : [type];
    const kinds = new Set(members.map((t) => this.kind(t)));
    if (!kinds.delete("empty")) return kinds;
    if (!kinds.has("bag") && !kinds.has("table")) kinds.add("array");
    return kinds;
  }

  private kind(type: Type): Kind {
    if (type.isIntersectionType()) {
      if (type.getTypes().some((t) => t.getSymbol()?.name === "DateBrand")) return "date";
      // A value of `string & Brand` is a string, and one of several object types is an object.
      const kinds = new Set(type.getTypes().map((t) => this.kind(t)));
      kinds.delete("object");
      const [kind, ...rest] = kinds;
      return kind === undefined ? "object" : rest.length === 0 && scalars.has(kind) ? kind : "other";
    }
    const { flags } = type;
    if (flags & TypeFlags.StringLike) return "string";
    if (flags & TypeFlags.NumberLike) return "number";
    if (flags & TypeFlags.BooleanLike) return "boolean";
    if (flags & TypeFlags.Null) return "null";
    if (flags & (TypeFlags.Undefined | TypeFlags.Void)) return "undefined";
    if (!(flags & TypeFlags.Object)) return "other";
    const name = type.getSymbol()?.name;
    if (name === "Table") return "table";
    if (name === "Bag" || name === "BagValue") return "bag";
    if (name === "Emit") return "emit";
    const { checker } = this.source;
    if (checker.isArrayType(type) || checker.isTupleType(type)) {
      const elements = checker.getTypeArguments(type as TypeReference);
      return elements.every((t) => t.flags & TypeFlags.Never) ? "empty" : "array";
    }
    if (checker.getSignaturesOfType(type, SignatureKind.Call).length > 0) return "other";
    return "object";
  }

  /** The one kind of `node` apart from null and undefined, or undefined when it has several or none. */
  private present(node: Node): Kind | undefined {
    const kinds = [...this.kinds(node)].filter((k) => k !== "null" && k !== "undefined");
    const [kind] = kinds;
    return kinds.every((k) => k === kind) ? kind : undefined;
  }

  /** The kind of `node`, which may be neither null nor undefined. */
  private only(node: Node): Kind | undefined {
    const kinds = this.kinds(node);
    const [kind] = kinds;
    return kinds.size === 1 ? kind : undefined;
  }

  /** Fails on an async or generator function, whose call returns an object however its body ends. */
  private synchronous(f: Helper | SpecFunctionNode): void {
    if (f.modifiers?.some((m) => m.kind === SyntaxKind.AsyncKeyword) || (!isArrowFunction(f) && f.asteriskToken))
      this.fail(f, "is async or a generator");
  }

  /** The declaration of the value that `name` reads outside the function, through imports. */
  private declarationOf(name: Identifier): Node | undefined {
    const { checker } = this.source;
    const symbol = checker.getSymbolAtLocation(name);
    const target = symbol !== undefined && symbol.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
    return target?.valueDeclaration?.resolve();
  }

  /** The value of the const that `name` reads, unless it is declared otherwise. */
  private constValue(name: Identifier): Expression | undefined {
    const d = this.declarationOf(name);
    if (d === undefined || !isVariableDeclaration(d) || !isVariableDeclarationList(d.parent)) return undefined;
    return d.parent.flags & NodeFlags.Const && d.initializer !== undefined ? unwrapped(d.initializer) : undefined;
  }

  /** Whether `callee` is tazuna's `condition` of a service, which returns its function as it is. */
  private isConditionWrapper(callee: Expression): boolean {
    const d = isIdentifier(callee) ? this.declarationOf(callee) : undefined;
    if (d === undefined || !isBindingElement(d)) return false;
    const key = d.propertyName ?? d.name;
    const declaration = d.parent.parent;
    if (key === undefined || !isIdentifier(key) || key.text !== "condition" || !isVariableDeclaration(declaration))
      return false;
    const definer = declaration.initializer === undefined ? undefined : unwrapped(declaration.initializer);
    const service = definer !== undefined && isCallExpression(definer) ? unwrapped(definer.expression) : undefined;
    const declared = service !== undefined && isIdentifier(service) ? this.declarationOf(service) : undefined;
    return declared !== undefined && isTazunaModule(declared.getSourceFile().fileName, "dsl/service");
  }

  /** The function that `name` reads outside the function, which the converter inlines where it is called. */
  private helper(name: Identifier): Helper | undefined {
    const d = this.declarationOf(name);
    if (d !== undefined && isFunctionDeclaration(d)) return d.body === undefined ? undefined : d;
    const value = this.constValue(name);
    if (value !== undefined && (isArrowFunction(value) || isFunctionExpression(value))) return value;
    if (value === undefined || !isCallExpression(value) || !this.isConditionWrapper(unwrapped(value.expression)))
      return undefined;
    const [f, ...rest] = value.arguments;
    const wrapped = f === undefined || rest.length > 0 ? undefined : unwrapped(f);
    return wrapped !== undefined && (isArrowFunction(wrapped) || isFunctionExpression(wrapped)) ? wrapped : undefined;
  }

  /**
   * The body of the helper that `e` calls, under its parameters. The arguments evaluate first, in order, as a call
   * evaluates them before the body runs; a name that the body reads is the helper's, never the caller's.
   */
  private inlined(callee: Identifier, e: CallExpression, scope: Scope): Expr {
    const f = this.helper(callee);
    if (f === undefined) this.fail(e, "calls a function outside the IR");
    if (this.inlining.includes(f)) this.fail(e, "calls a helper recursively");
    this.synchronous(f);
    if (e.arguments.length !== f.parameters.length) this.fail(e, "calls a helper with other than its parameters");
    this.inlining.push(f);
    try {
      const lets: (readonly [string, Expr])[] = [];
      const passed = e.arguments.map((a) => {
        if (isSpreadElement(a)) this.fail(a, "spreads arguments");
        const u = unwrapped(a);
        const kind = isIdentifier(u) ? scope.get(u.text) : undefined;
        if (kind === "args" || kind === "records") return kind;
        if (kind === "createKey") this.fail(a, "passes createKey");
        const name = `#${this.fresh++}`;
        lets.push([name, this.expression(a, scope)]);
        return name;
      });
      const bind = (i: number, inner: Scope): Expr => {
        const p = f.parameters[i];
        if (p === undefined) {
          const body = f.body as NonNullable<Helper["body"]>;
          return isBlock(body) ? this.block([...body.statements], inner) : this.expression(body, inner);
        }
        if (p.dotDotDotToken !== undefined || p.initializer !== undefined)
          this.fail(p, "takes a parameter with a rest or a default");
        const given = passed[i] as string;
        if (given === "args" || given === "records") {
          if (isIdentifier(p.name)) return bind(i + 1, new Map([...inner, [p.name.text, given]]));
          if (given === "records") this.fail(p, "destructures records");
          return this.fromArgs(p.name, inner, (s) => bind(i + 1, s));
        }
        return this.bound(p.name, { op: "var", name: given }, inner, (s) => bind(i + 1, s));
      };
      return lets.reduceRight<Expr>((body, [name, value]) => ({ op: "let", name, value, body }), bind(0, new Map()));
    } finally {
      this.inlining.pop();
    }
  }

  /**
   * The declaration of the value that `group` reads outside the function: a name, or a member of a contract, such as
   * `todo.todoConstants`, which the contract lists under the name it declares.
   */
  private outsideDeclaration(group: Expression, scope: Scope): Node | undefined {
    const g = unwrapped(group);
    if (isIdentifier(g)) return scope.has(g.text) ? undefined : this.declarationOf(g);
    if (!isPropertyAccessExpression(g) || !isIdentifier(g.name)) return undefined;
    const owner = unwrapped(g.expression);
    if (!isIdentifier(owner) || scope.has(owner.text)) return undefined;
    const { checker } = this.source;
    const member = checker.getSymbolAtLocation(g.name)?.valueDeclaration?.resolve();
    if (member === undefined) return undefined;
    if (isPropertyAssignment(member) && isIdentifier(member.initializer)) return this.declarationOf(member.initializer);
    const value = isShorthandPropertyAssignment(member) ? checker.getShorthandAssignmentValueSymbol(member) : undefined;
    const target = value !== undefined && value.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(value) : value;
    return target?.valueDeclaration?.resolve();
  }

  /** The field `name` of the `constants()` group that `group` reads, as a literal, when it is a scalar. */
  private constantField(group: Expression, name: string, e: Node, scope: Scope): Expr | undefined {
    const d = this.outsideDeclaration(group, scope);
    if (d === undefined || !isVariableDeclaration(d) || !isIdentifier(d.name)) return undefined;
    const values = this.defined.constants.get(definedKey(d.getSourceFile().fileName, d.name.text));
    if (values === undefined) return undefined;
    const value = values[name];
    const kind = this.only(e);
    if (value === undefined || typeof value === "object" || kind === undefined || !scalars.has(kind))
      this.fail(e, "reads a constant other than a scalar");
    return { op: "lit", value };
  }

  /** A const of a literal outside the function, as that literal; `parseInstant` of a literal is one. */
  private constLiteral(name: Identifier): Expr | undefined {
    const value = this.constValue(name);
    if (value === undefined) return undefined;
    const callee = isCallExpression(value) ? unwrapped(value.expression) : undefined;
    const literal =
      value.kind === SyntaxKind.TrueKeyword ||
      value.kind === SyntaxKind.FalseKeyword ||
      value.kind === SyntaxKind.NullKeyword ||
      isStringLiteral(value) ||
      isNoSubstitutionTemplateLiteral(value) ||
      isNumericLiteral(value) ||
      (callee !== undefined && isIdentifier(callee) && this.isTimeFunction(callee, "parseInstant"));
    return literal ? this.expression(value, new Map()) : undefined;
  }

  convertFunction(f: SpecFunctionNode, args: readonly Arg[]): Expr {
    this.synchronous(f);
    const [parameter, ...rest] = f.parameters;
    if (rest.length > 0) this.fail(f, "takes more than its arguments object");
    const written = f.body;
    if (written === undefined) this.fail(f, "has no body");
    const body = (scope: Scope): Expr => {
      if (isBlock(written)) return this.block([...written.statements], scope);
      return this.expression(written as Expression, scope);
    };
    this.specials = new Set(args.filter((a): a is Special => a === "records" || a === "createKey"));
    this.argument = (node, name) => {
      if (this.specials.has(name as Special)) this.fail(node, `reads ${name}`);
      // TS passes an arguments object without the name, whose field is undefined.
      if (!(args as readonly string[]).includes(name)) return { op: "undef" };
      if (name === "refs") return this.refsObject();
      return { op: "arg", arg: name as Exclude<Arg, Special | "refs"> };
    };
    if (parameter === undefined) return body(new Map());
    if (parameter.dotDotDotToken !== undefined || parameter.initializer !== undefined)
      this.fail(parameter, "takes its arguments with a rest or a default");
    if (isIdentifier(parameter.name)) return body(new Map([[parameter.name.text, "args"]]));
    return this.fromArgs(parameter.name, new Map(), body);
  }

  /** `refs`: the record of each top-level ref field of the input, looked up by the key that the field holds. */
  private refsObject(): Expr {
    const input: Expr = { op: "arg", arg: "input" };
    return {
      op: "obj",
      fields: [...this.refs].map(([name, entity]) => ({
        name,
        value: { op: "lookup", table: { op: "table", entity }, key: { op: "field", object: input, name } },
      })),
    };
  }

  /** `then` under the variables that `pattern` destructures from the arguments object. */
  private fromArgs(pattern: BindingName, scope: Scope, then: (scope: Scope) => Expr): Expr {
    return this.destructured(pattern, (name) => this.argument(pattern, name), scope, then, this.specials);
  }

  /** `then` under the variables that `pattern` binds from the fields that `field` reads. */
  private destructured(
    pattern: BindingName,
    field: (name: string) => Expr,
    scope: Scope,
    then: (scope: Scope) => Expr,
    specials: ReadonlySet<Special> = new Set(),
  ): Expr {
    if (!isObjectBindingPattern(pattern) || pattern.elements.length === 0)
      this.fail(pattern, "destructures other than a non-empty object pattern");
    const bind = (i: number, scope: Scope): Expr => {
      const element = pattern.elements[i];
      if (element === undefined) return then(scope);
      if (element.dotDotDotToken !== undefined || element.initializer !== undefined || element.name === undefined)
        this.fail(element, "destructures with a rest or a default");
      const key = element.propertyName ?? element.name;
      if (!isIdentifier(key)) this.fail(element, "destructures a computed name");
      if (specials.has(key.text as Special)) {
        if (!isIdentifier(element.name)) this.fail(element, `destructures ${key.text}`);
        return bind(i + 1, new Map([...scope, [element.name.text, key.text as Special]]));
      }
      const value = field(key.text);
      return this.bound(element.name, value, scope, (inner) => bind(i + 1, inner));
    };
    return bind(0, scope);
  }

  /** `then` with `name` bound to `value`. */
  private bound(name: BindingName, value: Expr, scope: Scope, then: (scope: Scope) => Expr): Expr {
    if (isIdentifier(name)) {
      return { op: "let", name: name.text, value, body: then(declared(scope, name.text)) };
    }
    const object = (field: string): Expr => ({ op: "field", object: value, name: field });
    return this.destructured(name, object, scope, then);
  }

  private block(statements: readonly Statement[], scope: Scope): Expr {
    const [statement, ...rest] = statements;
    if (statement === undefined) this.fail(this.source.node, "can end without a return");
    if (isReturnStatement(statement)) {
      if (statement.expression === undefined) this.fail(statement, "returns nothing");
      return this.expression(statement.expression, scope);
    }
    if (isVariableStatement(statement)) {
      const list = statement.declarationList;
      if (!(list.flags & NodeFlags.Const)) this.fail(statement, "declares a variable other than const");
      const declare = (i: number, scope: Scope): Expr => {
        const d = list.declarations[i];
        if (d === undefined) return this.block(rest, scope);
        if (d.initializer === undefined) this.fail(d, "declares a const without a value");
        const value = this.expression(d.initializer, scope);
        return this.bound(d.name, value, scope, (inner) => declare(i + 1, inner));
      };
      return declare(0, scope);
    }
    if (isIfStatement(statement)) {
      const branch = (s: Statement | undefined): Expr => {
        const own = s === undefined ? [] : isBlock(s) ? [...s.statements] : [s];
        const returns = own.length > 0 && isReturnStatement(own[own.length - 1] as Statement);
        if (!returns && own.some(isVariableStatement)) this.fail(statement, "declares in a branch that falls through");
        return this.block(returns ? own : [...own, ...rest], scope);
      };
      return {
        op: "ite",
        cond: this.expression(statement.expression, scope),
        yes: branch(statement.thenStatement),
        no: branch(statement.elseStatement),
      };
    }
    this.fail(statement, "has a statement other than const, if and return");
  }

  private expression(node: Expression, scope: Scope): Expr {
    const e = unwrapped(node);
    if (e.kind === SyntaxKind.TrueKeyword) return { op: "lit", value: true };
    if (e.kind === SyntaxKind.FalseKeyword) return { op: "lit", value: false };
    if (e.kind === SyntaxKind.NullKeyword) return { op: "lit", value: null };
    if (isStringLiteral(e) || isNoSubstitutionTemplateLiteral(e)) return { op: "lit", value: e.text };
    if (isNumericLiteral(e)) return this.number(e, Number(e.text));
    if (isIdentifier(e)) {
      const declaration = scope.get(e.text);
      if (declaration === "records") this.fail(e, "reads records other than an entity of it");
      if (declaration === "createKey") this.fail(e, "reads createKey other than by a call");
      if (declaration === "args") this.fail(e, "reads its arguments other than by a name");
      if (declaration === "variable") return { op: "var", name: e.text };
      if (e.text === "undefined") return { op: "undef" };
      const literal = this.constLiteral(e);
      if (literal !== undefined) return literal;
      this.fail(e, "reads a name declared outside the function");
    }
    if (isPrefixUnaryExpression(e)) {
      if (e.operator === SyntaxKind.ExclamationToken) return { op: "not", operand: this.expression(e.operand, scope) };
      const operand = unwrapped(e.operand);
      if (e.operator === SyntaxKind.MinusToken && isNumericLiteral(operand))
        return this.number(e, -Number(operand.text));
      if (e.operator === SyntaxKind.MinusToken && this.only(operand) === "number")
        return { op: "arith", operation: "sub", left: { op: "lit", value: 0 }, right: this.expression(operand, scope) };
      this.fail(e, "has a prefix operator other than !");
    }
    if (isConditionalExpression(e))
      return {
        op: "ite",
        cond: this.expression(e.condition, scope),
        yes: this.expression(e.whenTrue, scope),
        no: this.expression(e.whenFalse, scope),
      };
    if (isBinaryExpression(e)) return this.binary(e.left, e.operatorToken.kind, e.right, e, scope);
    if (isPropertyAccessExpression(e)) return this.access(e, scope);
    if (isObjectLiteralExpression(e)) return { op: "obj", fields: e.properties.map((p) => this.property(p, scope)) };
    if (isArrayLiteralExpression(e)) return this.array(e.elements, scope);
    if (isTemplateExpression(e)) this.fail(e, "writes a template literal");
    if (isCallExpression(e)) return this.call(e, scope);
    this.fail(e, "is no expression of the IR");
  }

  /** An array literal; each spread of an array is a concat, so the values keep the written order. */
  private array(elements: readonly Expression[], scope: Scope): Expr {
    const chunks: Expr[] = [];
    let values: Expr[] = [];
    for (const v of elements) {
      if (v.kind === SyntaxKind.OmittedExpression) this.fail(v, "skips in an array");
      if (!isSpreadElement(v)) {
        values.push(this.expression(v, scope));
        continue;
      }
      if (this.collection(v.expression) !== "array") this.fail(v, "spreads other than an array");
      if (values.length > 0) chunks.push({ op: "arr", values });
      values = [];
      chunks.push(this.expression(v.expression, scope));
    }
    if (chunks.length === 0) return { op: "arr", values };
    if (values.length > 0 || chunks.length === 1) chunks.push({ op: "arr", values });
    const [first, ...rest] = chunks as [Expr, ...Expr[]];
    return rest.reduce((left, right) => ({ op: "concat", left, right }), first);
  }

  private property(p: ObjectLiteralElementLike, scope: Scope): Field {
    if (isShorthandPropertyAssignment(p) && p.objectAssignmentInitializer === undefined && isIdentifier(p.name))
      return { name: p.name.text, value: this.expression(p.name, scope) };
    if (isPropertyAssignment(p) && (isIdentifier(p.name) || isStringLiteral(p.name)))
      return { name: p.name.text, value: this.expression(p.initializer, scope) };
    this.fail(p, "has an object member other than a named field");
  }

  private number(node: Node, n: number): Expr {
    if (!Number.isSafeInteger(n)) this.fail(node, "writes a number other than a safe integer");
    return { op: "lit", value: n };
  }

  private binary(left: Expression, operator: SyntaxKind, right: Expression, node: Node, scope: Scope): Expr {
    const both = () => ({ left: this.expression(left, scope), right: this.expression(right, scope) });
    if (operator === SyntaxKind.AmpersandAmpersandToken) return { op: "and", ...both() };
    if (operator === SyntaxKind.BarBarToken) return { op: "or", ...both() };
    if (operator === SyntaxKind.QuestionQuestionToken) return { op: "coalesce", ...both() };
    if (operator === SyntaxKind.PlusToken && (this.only(left) === "string" || this.only(right) === "string"))
      this.fail(node, "joins strings with +");
    if (operator === SyntaxKind.EqualsEqualsToken || operator === SyntaxKind.ExclamationEqualsToken) {
      const nullish = this.isNullish(right, scope) ? left : this.isNullish(left, scope) ? right : undefined;
      if (nullish === undefined) this.fail(node, "compares with == other than null or undefined");
      const name = `#${this.fresh++}`;
      const value: Expr = { op: "var", name };
      const isNullish: Expr = {
        op: "or",
        left: { op: "eq", left: value, right: { op: "lit", value: null } },
        right: { op: "eq", left: value, right: { op: "undef" } },
      };
      const body: Expr = operator === SyntaxKind.EqualsEqualsToken ? isNullish : { op: "not", operand: isNullish };
      return { op: "let", name, value: this.expression(nullish, scope), body };
    }
    const operation = arithmetic.get(operator);
    if (operation !== undefined) {
      if (this.only(left) !== "number" || this.only(right) !== "number")
        this.fail(node, "does arithmetic on other than numbers");
      return { op: "arith", operation, ...both() };
    }
    const negated = operator === SyntaxKind.ExclamationEqualsEqualsToken;
    const relation = relations.get(negated ? SyntaxKind.EqualsEqualsEqualsToken : operator);
    if (relation === undefined) this.fail(node, "has an operator outside the IR");
    const not = (e: Expr): Expr => (negated ? { op: "not", operand: e } : e);
    if (relation === "eq") {
      const scalar = (e: Expression) => [...this.kinds(e)].every((k) => scalars.has(k) || k === "date");
      if (!this.isNullish(left, scope) && !this.isNullish(right, scope) && !(scalar(left) && scalar(right)))
        this.fail(node, "compares with === other than scalars, null or undefined");
      return not({ op: "eq", ...both() });
    }
    const order = this.only(left);
    if ((order !== "number" && order !== "date") || this.only(right) !== order)
      this.fail(node, "orders other than two numbers or two dates");
    return { op: "compare", relation, order, ...both() };
  }

  /** Whether `e` is the literal null or undefined. */
  private isNullish(e: Expression, scope: Scope): boolean {
    const u = unwrapped(e);
    return u.kind === SyntaxKind.NullKeyword || (isIdentifier(u) && u.text === "undefined" && !scope.has(u.text));
  }

  /** Whether `node` is the records argument, by its name or as a field of the arguments object. */
  private isRecords(node: Expression, scope: Scope): boolean {
    const e = unwrapped(node);
    if (isIdentifier(e)) return scope.get(e.text) === "records";
    if (!isPropertyAccessExpression(e) || !isIdentifier(e.name) || e.name.text !== "records") return false;
    if (!this.specials.has("records")) return false;
    const object = unwrapped(e.expression);
    return isIdentifier(object) && scope.get(object.text) === "args";
  }

  private access(e: PropertyAccessExpression, scope: Scope): Expr {
    const optional = e.questionDotToken !== undefined;
    if (e.flags & NodeFlags.OptionalChain && !optional) this.fail(e, "continues an optional chain");
    if (!isIdentifier(e.name)) this.fail(e, "reads a private name");
    const name = e.name.text;
    if (this.isRecords(e.expression, scope)) {
      if (optional) this.fail(e, "reads an entity of records with ?.");
      return { op: this.only(e) === "table" ? "table" : "single", entity: name };
    }
    const target = unwrapped(e.expression);
    if (isIdentifier(target) && scope.get(target.text) === "args") {
      if (optional) this.fail(e, "reads its arguments with ?.");
      if (name === "records" && this.specials.has("records")) this.fail(e, "reads records other than an entity of it");
      if (name === "createKey") this.fail(e, "reads createKey other than by a call");
      return this.argument(e, name);
    }
    const constant = this.constantField(target, name, e, scope);
    if (constant !== undefined) return constant;
    const receiver = this.present(e.expression);
    const object = this.expression(e.expression, scope);
    const plain = (op: "strLen" | "size"): Expr => {
      if (optional) this.fail(e, `reads ${name} with ?.`);
      return op === "strLen" ? { op, string: object } : { op, collection: object };
    };
    if (name === "length" && receiver === "string") return plain("strLen");
    if (name === "length" && receiver === "array") return plain("size");
    if (name === "size" && (receiver === "bag" || receiver === "table")) return plain("size");
    if (receiver === "object" || (receiver === "emit" && (name === "kind" || name === "payload")))
      return { op: optional ? "fieldOpt" : "field", object, name };
    this.fail(e, `reads ${name} of a value outside the IR`);
  }

  private call(e: CallExpression, scope: Scope): Expr {
    if (e.flags & NodeFlags.OptionalChain) this.fail(e, "calls in an optional chain");
    const callee = unwrapped(e.expression);
    if (isIdentifier(callee) && callee.text === "emit" && !scope.has("emit")) return this.emitted(e, scope);
    if (this.isCreateKey(callee, scope)) return this.createKey(e);
    if (isIdentifier(callee) && !scope.has(callee.text) && this.isTimeFunction(callee, "parseInstant")) {
      const [text, ...more] = e.arguments;
      const literal = text === undefined ? undefined : unwrapped(text);
      if (
        literal === undefined ||
        more.length > 0 ||
        !(isStringLiteral(literal) || isNoSubstitutionTemplateLiteral(literal))
      )
        this.fail(e, "calls parseInstant with other than a string literal");
      try {
        return { op: "lit", value: parseInstant(literal.text) };
      } catch {
        this.fail(e, "calls parseInstant with a text that it rejects");
      }
    }
    if (isIdentifier(callee) && !scope.has(callee.text) && this.isTimeFunction(callee, "addDays")) {
      const [date, days, ...more] = e.arguments;
      if (date === undefined || days === undefined || more.length > 0 || this.only(date) !== "date")
        this.fail(e, "calls addDays with other than a date and days");
      if (this.only(days) !== "number") this.fail(e, "calls addDays with other than a number of days");
      return { op: "addDays", date: this.expression(date, scope), days: this.expression(days, scope) };
    }
    if (isIdentifier(callee) && callee.text !== "Boolean" && !scope.has(callee.text))
      return this.inlined(callee, e, scope);
    if (e.arguments.length === 0 && isPropertyAccessExpression(callee) && isIdentifier(callee.name)) {
      const receiver = this.only(callee.expression);
      if (callee.name.text === "only" && (receiver === "bag" || receiver === "table"))
        return { op: "only", collection: this.expression(callee.expression, scope) };
    }
    const [argument, ...rest] = e.arguments;
    if (argument === undefined || rest.length > 0) this.fail(e, "calls with other than one argument");
    if (isIdentifier(callee) && callee.text === "Boolean" && !scope.has("Boolean"))
      return { op: "not", operand: { op: "not", operand: this.expression(argument, scope) } };
    if (!isPropertyAccessExpression(callee) || !isIdentifier(callee.name))
      this.fail(e, "calls a function outside the IR");
    const method = callee.name.text;
    const receiver = this.only(callee.expression);
    if ((method === "startsWith" || method === "endsWith" || method === "includes") && receiver === "string") {
      if (this.only(argument) !== "string") this.fail(e, `calls ${method} with other than a string`);
      return {
        op: stringSearches[method],
        string: this.expression(callee.expression, scope),
        search: this.expression(argument, scope),
      };
    }
    if (method === "includes" && receiver === "array") {
      if (![...this.kinds(argument)].every((k) => scalars.has(k)))
        this.fail(e, "calls includes with other than a scalar");
      return {
        op: "includes",
        array: this.expression(callee.expression, scope),
        value: this.expression(argument, scope),
      };
    }
    if (method === "get" && receiver === "table") {
      // A key of several fields is an object.
      const key = this.only(argument);
      if (key !== "string" && key !== "object") this.fail(e, "gets a record by other than a string or a key object");
      return { op: "lookup", table: this.expression(callee.expression, scope), key: this.expression(argument, scope) };
    }
    const collection = this.collection(callee.expression);
    if ((method === "filter" || method === "some" || method === "every" || method === "map") && collection)
      return { op: method, visit: collection, ...this.visited(method, callee.expression, argument, scope) };
    if (method === "sum" && collection === "bag")
      return { op: "sum", ...this.visited(method, callee.expression, argument, scope) };
    if ((method === "min" || method === "max" || method === "sortedBy") && collection === "bag") {
      const key = this.only(this.callbackBody(method, argument));
      if (key !== "number" && key !== "date") this.fail(e, `calls ${method} with other than a key`);
      return { op: method, order: key, ...this.visited(method, callee.expression, argument, scope) };
    }
    if ((method === "minBy" || method === "maxBy") && collection === "bag") {
      const key = this.only(this.callbackBody(method, argument));
      if (key !== "number" && key !== "date") this.fail(e, `calls ${method} with other than a key`);
      // The value whose key is the least (greatest): the one value of that key, so that a tie is Fault.notOnly.
      const visited = this.visited(method, callee.expression, argument, scope);
      const extreme = `#${this.fresh++}`;
      const atExtreme: Expr = { op: "eq", left: visited.body, right: { op: "var", name: extreme } };
      return {
        op: "let",
        name: extreme,
        value: { op: method === "minBy" ? "min" : "max", order: key, ...visited },
        body: { op: "only", collection: { op: "filter", visit: "bag", ...visited, body: atExtreme } },
      };
    }
    if (method === "concat" && collection === "bag") {
      const other = this.only(argument);
      if (other !== "bag" && other !== "table" && other !== "array")
        this.fail(e, "concats other than a Bag or an array");
      return { op: "concat", left: this.expression(callee.expression, scope), right: this.expression(argument, scope) };
    }
    this.fail(e, `calls ${method}, which the IR has not`);
  }

  /** How a callback method visits `node`: as an array, or as a Bag, which a table is. */
  private collection(node: Node): "array" | "bag" | undefined {
    const kinds = [...this.kinds(node)];
    if (kinds.every((k) => k === "array")) return "array";
    return kinds.every((k) => k === "bag" || k === "table") ? "bag" : undefined;
  }

  /** Whether `callee` is createKey, by its name or as a field of the arguments object. */
  /** Whether `callee` is tazuna's time function `name`, which the converter evaluates itself. */
  private isTimeFunction(callee: Identifier, name: string): boolean {
    const d = this.declarationOf(callee);
    return (
      d !== undefined &&
      isFunctionDeclaration(d) &&
      d.name?.text === name &&
      isTazunaModule(d.getSourceFile().fileName, "data/time")
    );
  }

  private isCreateKey(callee: Expression, scope: Scope): boolean {
    if (isIdentifier(callee)) return scope.get(callee.text) === "createKey";
    if (!isPropertyAccessExpression(callee) || !isIdentifier(callee.name) || callee.name.text !== "createKey")
      return false;
    const object = unwrapped(callee.expression);
    return isIdentifier(object) && scope.get(object.text) === "args" && this.specials.has("createKey");
  }

  /**
   * `createKey(r)`, where `r` is written as `ref(E)` of an entity `E`, directly or through consts and object fields. A
   * key made in a callback would follow the order that the collection visits, so createKey stays out of callbacks.
   */
  private createKey(e: CallExpression): Expr {
    if (this.callbacks > 0) this.fail(e, "calls createKey in a callback");
    const [r, ...rest] = e.arguments;
    const entity = r === undefined || rest.length > 0 ? undefined : this.refEntity(r, new Set());
    if (entity === undefined) this.fail(e, "calls createKey with other than ref() of an entity");
    return { op: "createKey", entity };
  }

  /** The entity that `node` is ref() of, following consts and object fields to the ref() call. */
  private refEntity(node: Expression, seen: Set<Node>): string | undefined {
    const e = unwrapped(node);
    if (seen.has(e)) return undefined;
    seen.add(e);
    if (isIdentifier(e)) {
      const value = this.constValue(e);
      return value === undefined ? undefined : this.refEntity(value, seen);
    }
    if (isPropertyAccessExpression(e) && isIdentifier(e.name)) {
      const d = this.source.checker.getSymbolAtLocation(e.name)?.valueDeclaration?.resolve();
      if (d !== undefined && isPropertyAssignment(d)) return this.refEntity(d.initializer, seen);
      if (d !== undefined && isShorthandPropertyAssignment(d) && isIdentifier(d.name))
        return this.refEntity(d.name, seen);
      return undefined;
    }
    if (!isCallExpression(e) || e.arguments.length !== 1) return undefined;
    const callee = unwrapped(e.expression);
    const ref = isIdentifier(callee) ? this.declarationOf(callee) : undefined;
    if (ref === undefined || !isFunctionDeclaration(ref) || ref.name?.text !== "ref") return undefined;
    if (!isTazunaModule(ref.getSourceFile().fileName, "dsl/entity")) return undefined;
    const target = unwrapped(e.arguments[0] as Expression);
    const d = isIdentifier(target) ? this.declarationOf(target) : undefined;
    if (d === undefined || !isVariableDeclaration(d) || !isIdentifier(d.name)) return undefined;
    return this.defined.entities.get(definedKey(d.getSourceFile().fileName, d.name.text));
  }

  /** The arrow function that a callback method takes, with one plain parameter. */
  private callback(method: string, callback: Expression): ArrowFunction {
    const f = unwrapped(callback);
    if (!isArrowFunction(f)) this.fail(f, `calls ${method} with other than an arrow function`);
    this.synchronous(f);
    const [parameter, ...rest] = f.parameters;
    if (parameter === undefined || rest.length > 0 || parameter.dotDotDotToken !== undefined || parameter.initializer)
      this.fail(f, `calls ${method} with other than one plain parameter`);
    return f;
  }

  /** The expression that a callback returns, whose type is the key of min, max and sortedBy. */
  private callbackBody(method: string, callback: Expression): Expression {
    const f = this.callback(method, callback);
    if (isBlock(f.body)) this.fail(f, `calls ${method} with a block body`);
    return f.body as Expression;
  }

  private visited(
    method: string,
    collection: Expression,
    callback: Expression,
    scope: Scope,
  ): { readonly collection: Expr; readonly name: string; readonly body: Expr } {
    const f = this.callback(method, callback);
    const parameter = f.parameters[0] as NonNullable<(typeof f.parameters)[0]>;
    const body = (inner: Scope): Expr =>
      isBlock(f.body) ? this.block([...f.body.statements], inner) : this.expression(f.body as Expression, inner);
    const name = isIdentifier(parameter.name) ? parameter.name.text : `$${f.pos}`;
    const inner = declared(scope, name);
    const converted = this.expression(collection, scope);
    this.callbacks++;
    try {
      return {
        collection: converted,
        name,
        body: isIdentifier(parameter.name) ? body(inner) : this.bound(parameter.name, { op: "var", name }, inner, body),
      };
    } finally {
      this.callbacks--;
    }
  }
}

/**
 * The IR of the function of `source` that receives `args`, or the construct outside the IR that it has. A decide's
 * `events` are those its command lists; `refs` names the entity of each top-level ref field of the input.
 */
export function converted(
  source: Source,
  args: readonly Arg[],
  events: readonly DefinitionRef[] = [],
  defined: Defined = { constants: new Map(), entities: new Map() },
  refs: ReadonlyMap<string, string> = new Map(),
): Expr | { readonly unconverted: string } {
  try {
    return new Conversion(source, events, defined, refs).convertFunction(source.node, args);
  } catch (error) {
    if (error instanceof Unconverted) return { unconverted: error.message };
    throw error;
  }
}
