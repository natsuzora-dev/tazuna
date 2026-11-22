import {
  type ArrowFunction,
  type BindingName,
  type CallExpression,
  type Expression,
  type FunctionExpression,
  isArrayLiteralExpression,
  isArrowFunction,
  isAsExpression,
  isBinaryExpression,
  isBlock,
  isCallExpression,
  isConditionalExpression,
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
  isVariableStatement,
  type Node,
  NodeFlags,
  type ObjectLiteralElementLike,
  type PropertyAccessExpression,
  type Statement,
  SyntaxKind,
} from "typescript/unstable/ast";
import { SignatureKind, type Type, TypeFlags } from "typescript/unstable/sync";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Expr, Field } from "./ir.generated.ts";
import type { Source } from "./sources.ts";

/** An argument of a spec function: one that the IR names, or `records`, which only the record operations read. */
export type Arg = Extract<Expr, { readonly op: "arg" }>["arg"] | "records";
type Relation = Extract<Expr, { readonly op: "compare" }>["relation"];
type Order = Extract<Expr, { readonly op: "compare" }>["order"];

/** What the converter tells apart in a TS type: a member of a union, by how the IR reads its JSON. */
type Kind =
  | "string"
  | "number"
  | "boolean"
  | "null"
  | "undefined"
  | "instant"
  | "date"
  | "array"
  | "bag"
  | "table"
  | "emit"
  | "object"
  | "other";

const scalars: ReadonlySet<Kind> = new Set(["string", "number", "boolean", "null", "undefined"]);

/** A construct outside the IR, with the source text it is in. */
class Unconverted extends Error {}

/** The names that a function body can read: a variable, or the records argument. */
type Scope = ReadonlyMap<string, "variable" | "records">;

const declared = (scope: Scope, name: string): Scope => new Map([...scope, [name, "variable"]]);

const flipped: Readonly<Record<Relation, Relation>> = { lt: "gt", le: "ge", gt: "lt", ge: "le", eq: "eq" };

const relations: ReadonlyMap<SyntaxKind, Relation> = new Map([
  [SyntaxKind.LessThanToken, "lt"],
  [SyntaxKind.LessThanEqualsToken, "le"],
  [SyntaxKind.GreaterThanToken, "gt"],
  [SyntaxKind.GreaterThanEqualsToken, "ge"],
  [SyntaxKind.EqualsEqualsEqualsToken, "eq"],
]);

const temporalCompares: ReadonlyMap<string, Order> = new Map([
  ["Temporal.Instant.compare", "instant"],
  ["Temporal.PlainDate.compare", "date"],
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

  constructor(source: Source, events: readonly DefinitionRef[]) {
    this.source = source;
    this.events = events;
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
    return this.source.text.slice(node.pos, node.end).trim();
  }

  private fail(node: Node, reason: string): never {
    throw new Unconverted(`${reason}: ${this.text(node)}`);
  }

  private kinds(node: Node): ReadonlySet<Kind> {
    const type = this.source.checker.getTypeAtLocation(node);
    if (type === undefined) return new Set(["other"]);
    const members = type.isUnionType() ? type.getTypes() : [type];
    return new Set(members.map((t) => this.kind(t)));
  }

  private kind(type: Type): Kind {
    const { flags } = type;
    if (flags & TypeFlags.StringLike) return "string";
    if (flags & TypeFlags.NumberLike) return "number";
    if (flags & TypeFlags.BooleanLike) return "boolean";
    if (flags & TypeFlags.Null) return "null";
    if (flags & (TypeFlags.Undefined | TypeFlags.Void)) return "undefined";
    if (!(flags & TypeFlags.Object)) return "other";
    const name = type.getSymbol()?.name;
    if (name === "Instant") return "instant";
    if (name === "PlainDate") return "date";
    if (name === "Table") return "table";
    if (name === "Bag" || name === "BagValue") return "bag";
    if (name === "Emit") return "emit";
    const { checker } = this.source;
    if (checker.isArrayType(type) || checker.isTupleType(type)) return "array";
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
  private synchronous(f: ArrowFunction | FunctionExpression): void {
    if (f.modifiers?.some((m) => m.kind === SyntaxKind.AsyncKeyword) || (isFunctionExpression(f) && f.asteriskToken))
      this.fail(f, "is async or a generator");
  }

  convertFunction(f: ArrowFunction | FunctionExpression, args: readonly Arg[]): Expr {
    this.synchronous(f);
    const [parameter, ...rest] = f.parameters;
    if (rest.length > 0) this.fail(f, "takes more than its arguments object");
    const body = (scope: Scope): Expr =>
      isBlock(f.body) ? this.block([...f.body.statements], scope) : this.expression(f.body as Expression, scope);
    if (parameter === undefined) return body(new Map());
    if (parameter.dotDotDotToken !== undefined || parameter.initializer !== undefined)
      this.fail(parameter, "takes its arguments with a rest or a default");
    if (!isObjectBindingPattern(parameter.name)) this.fail(parameter, "takes its arguments without destructuring");
    const named = (name: string): Expr => {
      if (!(args as readonly string[]).includes(name) || name === "records") this.fail(parameter, `reads ${name}`);
      return { op: "arg", arg: name as Exclude<Arg, "records"> };
    };
    return this.destructured(parameter.name, named, new Map(), body, args.includes("records"));
  }

  /** `then` under the variables that `pattern` binds from the fields that `field` reads. */
  private destructured(
    pattern: BindingName,
    field: (name: string) => Expr,
    scope: Scope,
    then: (scope: Scope) => Expr,
    records = false,
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
      if (records && key.text === "records") {
        if (!isIdentifier(element.name)) this.fail(element, "destructures records");
        return bind(i + 1, new Map([...scope, [element.name.text, "records"]]));
      }
      const value = field(key.text);
      return this.bound(element.name, value, scope, (inner) => bind(i + 1, inner));
    };
    return bind(0, scope);
  }

  /** `then` with `name` bound to `value`. */
  private bound(name: BindingName, value: Expr, scope: Scope, then: (scope: Scope) => Expr): Expr {
    if (isIdentifier(name)) return { op: "let", name: name.text, value, body: then(declared(scope, name.text)) };
    return this.destructured(name, (field) => ({ op: "field", object: value, name: field }), scope, then);
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
        return this.bound(d.name, this.expression(d.initializer, scope), scope, (inner) => declare(i + 1, inner));
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
      if (declaration === "variable") return { op: "var", name: e.text };
      if (e.text === "undefined") return { op: "undef" };
      this.fail(e, "reads a name declared outside the function");
    }
    if (isPrefixUnaryExpression(e)) {
      if (e.operator === SyntaxKind.ExclamationToken) return { op: "not", operand: this.expression(e.operand, scope) };
      const operand = unwrapped(e.operand);
      if (e.operator === SyntaxKind.MinusToken && isNumericLiteral(operand))
        return this.number(e, -Number(operand.text));
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
    if (isArrayLiteralExpression(e))
      return {
        op: "arr",
        values: e.elements.map((v) => {
          if (isSpreadElement(v) || v.kind === SyntaxKind.OmittedExpression)
            this.fail(v, "spreads or skips in an array");
          return this.expression(v, scope);
        }),
      };
    if (isCallExpression(e)) return this.call(e, scope);
    this.fail(e, "is no expression of the IR");
  }

  private property(p: ObjectLiteralElementLike, scope: Scope): Field {
    if (isShorthandPropertyAssignment(p) && p.objectAssignmentInitializer === undefined && isIdentifier(p.name))
      return { name: p.name.text, value: this.expression(p.name, scope) };
    if (isPropertyAssignment(p) && (isIdentifier(p.name) || isStringLiteral(p.name)))
      return { name: p.name.text, value: this.expression(p.initializer, scope) };
    this.fail(p, "has an object member other than a named field");
  }

  private number(node: Node, n: number): Expr {
    if (!Number.isFinite(n)) this.fail(node, "writes a number that JSON cannot hold");
    return { op: "lit", value: n };
  }

  private binary(left: Expression, operator: SyntaxKind, right: Expression, node: Node, scope: Scope): Expr {
    const both = () => ({ left: this.expression(left, scope), right: this.expression(right, scope) });
    if (operator === SyntaxKind.AmpersandAmpersandToken) return { op: "and", ...both() };
    if (operator === SyntaxKind.BarBarToken) return { op: "or", ...both() };
    if (operator === SyntaxKind.QuestionQuestionToken) return { op: "coalesce", ...both() };
    const negated = operator === SyntaxKind.ExclamationEqualsEqualsToken;
    const relation = relations.get(negated ? SyntaxKind.EqualsEqualsEqualsToken : operator);
    if (relation === undefined) this.fail(node, "has an operator outside the IR");
    const not = (e: Expr): Expr => (negated ? { op: "not", operand: e } : e);
    const temporal =
      this.temporalCompare(left, right, relation, scope) ?? this.temporalCompare(right, left, flipped[relation], scope);
    if (temporal !== undefined) return not(temporal);
    if (relation === "eq") {
      const literal = (e: Expression) => {
        const u = unwrapped(e);
        return u.kind === SyntaxKind.NullKeyword || (isIdentifier(u) && u.text === "undefined" && !scope.has(u.text));
      };
      const scalar = (e: Expression) => [...this.kinds(e)].every((k) => scalars.has(k));
      if (!literal(left) && !literal(right) && !(scalar(left) && scalar(right)))
        this.fail(node, "compares with === other than scalars, null or undefined");
      return not({ op: "eq", ...both() });
    }
    if (this.only(left) !== "number" || this.only(right) !== "number") this.fail(node, "orders other than numbers");
    return { op: "compare", relation, order: "number", ...both() };
  }

  /** `Temporal.X.compare(a, b) relation 0`, when `call` is that call and `zero` is 0. */
  private temporalCompare(call: Expression, zero: Expression, relation: Relation, scope: Scope): Expr | undefined {
    const c = unwrapped(call);
    const z = unwrapped(zero);
    if (!isCallExpression(c) || !isNumericLiteral(z) || Number(z.text) !== 0) return undefined;
    const order = temporalCompares.get(this.text(c.expression));
    if (order === undefined) return undefined;
    const [a, b, ...rest] = c.arguments;
    if (a === undefined || b === undefined || rest.length > 0 || this.only(a) !== order || this.only(b) !== order)
      this.fail(c, `compares other than two ${order}s`);
    return { op: "compare", relation, order, left: this.expression(a, scope), right: this.expression(b, scope) };
  }

  private access(e: PropertyAccessExpression, scope: Scope): Expr {
    const optional = e.questionDotToken !== undefined;
    if (e.flags & NodeFlags.OptionalChain && !optional) this.fail(e, "continues an optional chain");
    if (!isIdentifier(e.name)) this.fail(e, "reads a private name");
    const name = e.name.text;
    const records = unwrapped(e.expression);
    if (isIdentifier(records) && scope.get(records.text) === "records") {
      if (optional) this.fail(e, "reads an entity of records with ?.");
      return { op: this.only(e) === "table" ? "table" : "single", entity: name };
    }
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
    if (method === "equals" && (receiver === "instant" || receiver === "date")) {
      if (this.only(argument) !== receiver) this.fail(e, `calls equals with other than a ${receiver}`);
      return {
        op: "compare",
        relation: "eq",
        order: receiver,
        left: this.expression(callee.expression, scope),
        right: this.expression(argument, scope),
      };
    }
    if (method === "get" && receiver === "table") {
      if (this.only(argument) !== "string") this.fail(e, "gets a record by other than a string");
      return { op: "lookup", table: this.expression(callee.expression, scope), key: this.expression(argument, scope) };
    }
    const collection = receiver === "array" ? "array" : receiver === "bag" || receiver === "table" ? "bag" : undefined;
    if ((method === "filter" || method === "some" || method === "every" || method === "map") && collection)
      return { op: method, visit: collection, ...this.visited(method, callee.expression, argument, scope) };
    if (method === "sum" && collection === "bag")
      return { op: "sum", ...this.visited(method, callee.expression, argument, scope) };
    if ((method === "min" || method === "max" || method === "sortedBy") && collection === "bag") {
      const key = this.only(this.callbackBody(method, argument));
      if (key !== "number" && key !== "instant" && key !== "date")
        this.fail(e, `calls ${method} with other than a key`);
      return { op: method, order: key, ...this.visited(method, callee.expression, argument, scope) };
    }
    if (method === "concat" && collection === "bag") {
      const other = this.only(argument);
      if (other !== "bag" && other !== "table" && other !== "array")
        this.fail(e, "concats other than a Bag or an array");
      return { op: "concat", left: this.expression(callee.expression, scope), right: this.expression(argument, scope) };
    }
    this.fail(e, `calls ${method}, which the IR has not`);
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
    return {
      collection: this.expression(collection, scope),
      name,
      body: isIdentifier(parameter.name) ? body(inner) : this.bound(parameter.name, { op: "var", name }, inner, body),
    };
  }
}

/**
 * The IR of the function of `source` that receives `args`, or the construct outside the IR that it has. A decide's
 * `events` are those its command lists.
 */
export function converted(
  source: Source,
  args: readonly Arg[],
  events: readonly DefinitionRef[] = [],
): Expr | { readonly unconverted: string } {
  try {
    return new Conversion(source, events).convertFunction(source.node, args);
  } catch (error) {
    if (error instanceof Unconverted) return { unconverted: error.message };
    throw error;
  }
}
