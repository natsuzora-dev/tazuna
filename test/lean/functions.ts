import { Bag, comparable as comparableValue, Runs } from "../../src/data/canonical.ts";
import type { Answer } from "../../src/data/trace.generated.ts";
import { canonicalJson, encode, type Fields, objectOf, type Shape, strictObjectOf } from "../../src/data/values.ts";
import { thrown } from "../../src/data/violation.ts";
import type { AnyCommand, AnyEvent, AnyQuery, Automation, Named, ServiceDefinition } from "../../src/dsl/definition.ts";
import type { AnyEntity } from "../../src/dsl/entity.ts";
import type { Spec } from "../../src/load/load.ts";
import { refOfDefinition } from "../../src/load/traceName.ts";
import { SpecFunctions } from "../../src/run/functions.ts";
import {
  type Access,
  type Assignment,
  type CopyScope,
  Failed,
  type Holder,
  type Issue,
  type Scope,
} from "../../src/semantics/functions.ts";
import type { Emit } from "../../src/semantics/message.ts";
import type { Schema } from "../../src/semantics/service/basic.ts";
import { type RecordSource, reversedKeys } from "../../src/semantics/service/records.ts";
import { type TransitionStructure, traceNameOfRef, transitionRef } from "../../src/syntax/structure.ts";
import type { Message } from "./lean.ts";

const json = (value: unknown): unknown => (value === undefined ? undefined : JSON.parse(JSON.stringify(value)));

/**
 * Returns `f()`, which decodes a value of Lean's message, or, when it throws, a `thrown` failure of `schema`, as in
 * src/run.
 */
function decoding<T>(f: () => T, schema?: Schema): T | Failed {
  try {
    return f();
  } catch (error) {
    return new Failed(schema === undefined ? { kind: "thrown" } : { kind: "thrown", schema }, thrown(error));
  }
}

/** Decodes `value`, an encoded value of `shape`. */
function decode(schema: Schema, shape: Shape, value: unknown): Fields | Failed {
  return decoding(() => objectOf(shape).parse(value) as Fields, schema);
}

/** Decodes `value` when it matches `shape` with no other fields, and returns undefined when it does not. */
function decodeStrict(schema: Schema, shape: Shape, value: unknown): Fields | undefined | Failed {
  const decoded = decoding(() => strictObjectOf(shape).safeParse(value), schema);
  if (decoded instanceof Failed) return decoded;
  return decoded.success ? (decoded.data as Fields) : undefined;
}

/**
 * Decodes each field of `row` by its schema in `shape`. A field that fails it, or that `shape` lacks, stays as it is.
 */
function decodeFields(shape: Shape, row: Fields): Fields | Failed {
  return decoding(() =>
    Object.fromEntries(
      Object.entries(row).map(([field, value]) => {
        const decoded = shape[field]?.safeParse(value);
        return [field, decoded?.success === true ? decoded.data : value];
      }),
    ),
  );
}

export type ReadRecord = (part: {
  readonly entity: string;
  readonly key?: string;
  readonly field?: string;
  readonly beforeEventWrite?: true;
}) => unknown;

export interface Answering {
  answer(message: Message): Message;
}

/** Tags each value with its shape for Lean. Objects become [name, value] pairs to keep their key order. */
function tagged(value: unknown): unknown {
  if (value instanceof Bag) return { bag: value.items.map(tagged) };
  if (value instanceof Runs) return { runs: value.runs.map(tagged) };
  if (Array.isArray(value)) return { arr: value.map(tagged) };
  if (value !== null && typeof value === "object")
    return {
      obj: Object.entries(value)
        .filter(([, v]) => v !== undefined)
        .map(([k, v]) => [k, tagged(v)]),
    };
  return { leaf: value };
}

export class VerifyFunctions implements Answering {
  private readonly spec: Spec;
  constructor(spec: Spec) {
    this.spec = spec;
  }

  answer(message: Message): Message {
    if (message["type"] !== "comparableValue") throw new Error(`verify asks no ${String(message["type"])}`);
    const ref = message["definition"] as { readonly kind: string; readonly service: string; readonly name: string };
    const found = this.spec.definitions.find(
      (d) => d.service === ref.service && d.name === ref.name && d.definition.kind === ref.kind,
    )?.definition;
    if (found === undefined) throw new Error(`no ${ref.kind} ${ref.service}.${ref.name}`);
    const shape = ((): Shape | undefined => {
      switch (message["part"]) {
        case "input":
          return (found as AnyCommand | AnyQuery).input;
        case "output":
          return (found as AnyCommand | AnyQuery).output;
        case "payload":
          return (found as AnyEvent).payload;
        default:
          return (found as { controls?: Record<string, { payload?: Shape }> }).controls?.[message["control"] as string]
            ?.payload;
      }
    })();
    return { type: "compared", value: tagged(comparableValue(shape, message["value"])) };
  }
}

interface Accessed {
  readonly holder: Holder;
  readonly name: string;
}

/** Lean's Scope as tazuna-lean sends it: without resource and owner; `shown` holds null before an answer. */
interface LeanScope {
  readonly machine: string;
  readonly state: string | null;
  readonly context: unknown;
  readonly copy: { readonly map: string; readonly key: unknown; readonly context: unknown } | null;
  readonly active: readonly string[];
  readonly shown: Readonly<Record<string, unknown>>;
  readonly input: unknown;
  readonly now: string;
}

/** Lean's Schema: names as the service's trace names where the TS Schema has refs. */
type LeanSchema =
  | { readonly kind: "input" | "output"; readonly definition: string }
  | { readonly kind: "payload"; readonly event: string }
  | { readonly kind: "control"; readonly screen: string; readonly control: string }
  | { readonly kind: "held"; readonly chart: string; readonly state: string; readonly name: string }
  | { readonly kind: "context"; readonly chart: string }
  | { readonly kind: "mapContext" | "mapKey"; readonly chart: string; readonly map: string };

/**
 * Carries Lean's questions to the spec functions of src/run: decodes Lean's values, answers with the same SpecFunctions
 * that the TS run asks, and sends an answer that failed as its Issue.
 */
export class RunFunctions implements Answering {
  private readonly spec: Spec;
  private readonly service: string;
  private readonly owner: ServiceDefinition;
  private readonly functions: SpecFunctions;
  private readonly records: RecordSource;
  private readonly before: RecordSource;

  constructor(spec: Spec, service: string, read: ReadRecord) {
    this.spec = spec;
    this.service = service;
    this.owner = spec.services.get(service)?.definition as ServiceDefinition;
    this.functions = new SpecFunctions(spec, service);
    const entities = this.owner.entities;
    const source = (before: object): RecordSource => ({
      keys: (entity) => read({ entity, ...before }) as string[],
      exists: (entity, key) => read({ entity, key, ...before }) as boolean,
      field: (entity, key, field) => {
        const value = read(key === undefined ? { entity, field, ...before } : { entity, key, field, ...before });
        const schema = (entities[entity]?.fields as Shape | undefined)?.[field];
        return value === undefined || schema === undefined ? value : schema.parse(value);
      },
    });
    this.records = source({});
    this.before = source({ beforeEventWrite: true });
  }

  private leanSchema(schema: Schema): LeanSchema {
    switch (schema.kind) {
      case "input":
      case "output":
        return { kind: schema.kind, definition: traceNameOfRef(schema.definition, this.service) };
      case "payload":
        return { kind: "payload", event: traceNameOfRef(schema.event, this.service) };
      case "control":
        return { kind: "control", screen: schema.screen.name, control: schema.control };
      case "held":
        return { kind: "held", chart: schema.chart.name, state: schema.state, name: schema.name };
      case "context":
        return { kind: "context", chart: schema.chart.name };
      case "mapContext":
      case "mapKey":
        return { kind: schema.kind, chart: schema.chart.name, map: schema.map };
    }
  }

  private schemaOf(lean: LeanSchema): Schema {
    const ref = ({ service, name }: Named<unknown>) => ({ service, name });
    switch (lean.kind) {
      case "input":
      case "output":
        return {
          kind: lean.kind,
          definition: ref(this.functions.definition(["command", "query", "screen"], lean.definition)),
        };
      case "payload":
        return { kind: "payload", event: ref(this.functions.definition(["event"], lean.event)) };
      case "control":
        return {
          kind: "control",
          screen: ref(this.functions.definition(["screen"], lean.screen)),
          control: lean.control,
        };
      default:
        throw new Error(`tazuna-lean sent a value of the ${lean.kind} schema`);
    }
  }

  private decoded(lean: LeanSchema, value: unknown): Fields | Failed {
    const schema = this.schemaOf(lean);
    return decode(schema, this.functions.shape(schema), value);
  }

  /** Decodes the input of a request to the command or query `name`. */
  private inputOf(name: string, value: unknown): Fields | Failed {
    return this.decoded({ kind: "input", definition: name }, value);
  }

  private issue(issue: Issue): Message {
    switch (issue.kind) {
      case "thrown":
        return issue.schema === undefined
          ? { kind: "thrown" }
          : { kind: "thrown", schema: this.leanSchema(issue.schema) };
      case "schema":
        return { kind: "schema", schema: this.leanSchema(issue.schema) };
      case "unheld":
      case "notOnly":
        return issue;
    }
  }

  /** Returns the reply of the value, or the Issue of a failed answer. */
  private replied<T>(value: T | Failed, reply: (value: T) => Message): Message {
    return value instanceof Failed ? { issue: this.issue(value.issue) } : reply(value);
  }

  private now(message: Message): Temporal.Instant {
    return Temporal.Instant.from(String(message["now"]));
  }

  private scopeOf(lean: LeanScope): Scope | Failed {
    const { named, ref } = this.functions.chartOf(lean.machine);
    const chart = named.definition;
    const context = decode({ kind: "context", chart: ref }, chart.context, lean.context);
    if (context instanceof Failed) return context;
    let copy: CopyScope | undefined;
    if (lean.copy !== null) {
      const { map } = lean.copy;
      const node = this.functions.node(lean.machine, map);
      const key = decode({ kind: "mapKey", chart: ref, map }, node?.key ?? {}, lean.copy.key);
      if (key instanceof Failed) return key;
      const own = decode({ kind: "mapContext", chart: ref, map }, node?.context ?? {}, lean.copy.context);
      if (own instanceof Failed) return own;
      copy = { map, key, context: own };
    }
    const shown = new Map<string, unknown>();
    for (const [slot, value] of Object.entries(lean.shown)) {
      const query = chart.queries?.[slot] as AnyQuery;
      const schema: Schema = { kind: "output", definition: refOfDefinition(this.spec, query) };
      const output = value === null ? null : decode(schema, query.output ?? {}, value);
      if (output instanceof Failed) return output;
      shown.set(slot, output);
    }
    const input =
      chart.kind === "screen" ? decode({ kind: "input", definition: ref }, chart.input ?? {}, lean.input) : {};
    if (input instanceof Failed) return input;
    return {
      machine: lean.machine,
      resource: lean.machine,
      owner: lean.machine,
      state: lean.state,
      context,
      copy,
      active: new Set(lean.active),
      shown,
      input,
      now: Temporal.Instant.from(lean.now),
    };
  }

  /** Returns the extra of the transition at `keys`, with its payload or output decoded. */
  private extraOf(machine: string, keys: readonly string[], extra: Fields): Fields | Failed {
    const { named, ref } = this.functions.chartOf(machine);
    const chart = named.definition;
    const [keyword, key = ""] = keys;
    if ("payload" in extra) {
      const schema: Schema =
        chart.controls?.[key] === undefined
          ? { kind: "payload", event: refOfDefinition(this.spec, chart.receives[key]) }
          : { kind: "control", screen: ref, control: key };
      const payload = decode(schema, this.functions.shape(schema), extra["payload"]);
      return payload instanceof Failed ? payload : { payload };
    }
    if ("output" in extra) {
      const target = (
        keyword === "calls" ? chart.queries?.[key] : keyword === "opens" ? chart.screens?.[key] : chart.commands[key]
      ) as { readonly output?: Shape };
      const shape = keyword === "opens" ? (target.output ?? {}) : target.output;
      if (shape === undefined) return extra;
      const output = decode({ kind: "output", definition: refOfDefinition(this.spec, target) }, shape, extra["output"]);
      return output instanceof Failed ? output : { output };
    }
    return extra;
  }

  /** Returns the reply of a Scope question about `message["scope"]`, with what its expressions read and assigned. */
  private scoped(message: Message, ask: (scope: Scope, access: Access) => Message): Message {
    const access = {
      context: [] as Accessed[],
      active: [] as Accessed[],
      assigned: [] as Accessed[],
      shown: [] as string[],
    };
    const told: Access = {
      context: (holder, name) => access.context.push({ holder, name }),
      active: (holder, name) => access.active.push({ holder, name }),
      assigned: (holder, name) => access.assigned.push({ holder, name }),
      shown: (slot) => access.shown.push(slot),
      now: () => {},
    };
    return { ...this.replied(this.scopeOf(message["scope"] as LeanScope), (scope) => ask(scope, told)), access };
  }

  answer(message: Message): Message {
    const value = message["value"];
    const failedReply = (failed: string | undefined): Message => (failed === undefined ? {} : { failed });
    switch (message["type"]) {
      case "parse": {
        const schema = this.schemaOf(message["schema"] as LeanSchema);
        return this.replied(this.functions.parse(schema, value), (parsed) =>
          "error" in parsed ? {} : { value: parsed.encoded },
        );
      }
      case "canonical": {
        const schema = this.schemaOf(message["schema"] as LeanSchema);
        return this.replied(this.functions.canonical(schema, value), (written) => ({ value: written }));
      }
      case "normalize": {
        const schema = this.schemaOf(message["schema"] as LeanSchema);
        // The value arrives as JSON, so it is decoded first.
        return this.replied(decodeStrict(schema, this.functions.shape(schema), value), (decoded) =>
          decoded === undefined
            ? {}
            : this.replied(this.functions.normalize(schema, decoded), (normalized) =>
                "error" in normalized ? {} : { value: normalized.encoded },
              ),
        );
      }
      case "binding": {
        const name = String(message["command"]);
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          this.replied(
            this.functions.binding(name, String(message["binding"]), input, this.records, this.now(message)),
            (bound) => ({ bound }),
          ),
        );
      }
      case "requirement": {
        const name = String(message["command"]);
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          this.replied(
            this.functions.requirement(name, String(message["condition"]), input, this.records, this.now(message)),
            (holds) => ({ holds }),
          ),
        );
      }
      case "inputRequirement": {
        const name = String(message["target"]);
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          this.replied(this.functions.inputRequirement(name, String(message["condition"]), input), (holds) => ({
            holds,
          })),
        );
      }
      case "decide": {
        const name = String(message["command"]);
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          this.replied(this.functions.decide(name, input, this.records, this.now(message)), (decided) => ({
            emits: decided.map((e) => ({ event: e.event, payload: json(e.payload) })),
          })),
        );
      }
      case "ensures": {
        const name = String(message["command"]);
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          this.replied(this.functions.ensures(name, input, this.before, this.records, this.now(message)), failedReply),
        );
      }
      case "queryEnsures": {
        const name = String(message["query"]);
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          this.replied(this.decoded({ kind: "output", definition: name }, message["output"]), (output) =>
            this.replied(this.functions.queryEnsures(name, input, output, this.records), failedReply),
          ),
        );
      }
      case "resultEnsures": {
        const name = String(message["target"]);
        const input = this.inputOf(name, message["input"]);
        if (input instanceof Failed) return this.replied(input, failedReply);
        const target = this.functions.definition<AnyCommand | AnyQuery>(["command", "query"], name).definition;
        const output =
          target.output === undefined
            ? undefined
            : this.decoded({ kind: "output", definition: name }, message["output"]);
        if (output instanceof Failed) return this.replied(output, failedReply);
        const events: Emit[] = [];
        for (const e of message["events"] as { event: string; payload: unknown }[]) {
          const payload = this.decoded({ kind: "payload", event: e.event }, e.payload);
          if (payload instanceof Failed) return this.replied(payload, failedReply);
          events.push({ event: e.event, payload });
        }
        return this.replied(this.functions.resultEnsures(name, input, output, events), failedReply);
      }
      case "invariant": {
        const name = String(message["entity"]);
        const fields = (this.owner.entities[name] as AnyEntity).fields as Shape;
        return this.replied(decodeFields(fields, message["record"] as Fields), (record) =>
          this.replied(this.functions.invariant(name, record), failedReply),
        );
      }
      case "serviceInvariant":
        return this.replied(this.functions.serviceInvariant(this.records), failedReply);
      case "chartInvariant":
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.chartInvariant(scope, this.records, access), failedReply),
        );
      case "resolve": {
        const name = String(message["query"]);
        const records = message["reversed"] === true ? reversedKeys(this.records) : this.records;
        return this.replied(this.inputOf(name, message["input"]), (input) =>
          // Lean's Value has no undefined, so an output that author code left undefined is sent as null.
          this.replied(this.functions.resolve(name, input, records, this.now(message)), (output) => ({
            output: json(output) ?? null,
          })),
        );
      }
      case "react": {
        const name = String(message["automation"]);
        const a = this.functions.definition<Automation>(["automation"], name).definition;
        const event = this.spec.names.get(Object.values(a.receives)[0]) as Named<AnyEvent>;
        const schema: Schema = { kind: "payload", event: { service: event.service, name: event.name } };
        const keys = Object.entries(message["keys"] as Record<string, number>);
        return this.replied(decode(schema, event.definition.payload, message["payload"]), (payload) =>
          this.replied(
            this.functions.react(name, payload, this.records, this.now(message), keys),
            ({ input, created }) => (input === undefined ? { created } : { input: json(input), created }),
          ),
        );
      }
      case "comparable":
        return this.replied(
          this.functions.comparable(String(message["query"]), message["answer"] as Answer),
          (compared) => ({ value: canonicalJson(compared) }),
        );
      case "initialContext": {
        const name = String(message["machine"]);
        const { named, ref } = this.functions.chartOf(name);
        const chart = named.definition;
        const input = decode({ kind: "input", definition: ref }, chart.input ?? {}, message["input"]);
        return this.replied(input, (decoded) =>
          this.replied(this.functions.initialContext(name, decoded), (context) => ({
            context: encode(chart.context, context),
          })),
        );
      }
      case "guard": {
        const t = message["transition"] as TransitionStructure;
        return this.scoped(message, (scope, access) =>
          this.replied(this.extraOf(scope.machine, t.keys, message["extra"] as Fields), (extra) =>
            this.replied(this.functions.guard(scope, this.records, transitionRef(t), extra, access), (passes) => ({
              passes,
            })),
          ),
        );
      }
      case "assign": {
        const at = message["at"] as
          | { readonly kind: "transition"; readonly transition: TransitionStructure }
          | { readonly kind: "entry" | "exit"; readonly state: string };
        const assignment: Assignment =
          at.kind === "transition" ? { kind: "transition", transition: transitionRef(at.transition) } : at;
        const transitionKeys = at.kind === "transition" ? at.transition.keys : [];
        const keys = Object.entries(message["keys"] as Record<string, number>);
        return this.scoped(message, (scope, access) =>
          this.replied(this.extraOf(scope.machine, transitionKeys, message["extra"] as Fields), (extra) =>
            this.replied(
              this.functions.assign(scope, this.records, assignment, extra, keys, access),
              ({ context, copyContext, created }) => {
                const { copy } = scope;
                const chart = this.functions.chartOf(scope.machine).named.definition;
                const shape = copy === undefined ? {} : (this.functions.node(scope.machine, copy.map)?.context ?? {});
                return {
                  context: encode(chart.context, context),
                  ...(copy === undefined ? {} : { copy: encode(shape, copyContext ?? copy.context) }),
                  created,
                };
              },
            ),
          ),
        );
      }
      case "input": {
        const activity = message["activity"] as { keyword: string; key: string };
        const keys = Object.entries(message["keys"] as Record<string, number>);
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.input(scope, this.records, activity, keys, access), ({ encoded, created }) => ({
            input: encoded,
            created,
          })),
        );
      }
      case "holds":
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.holds(scope, this.records, access), () => ({})),
        );
      case "deadlines":
        return {
          deadlines: this.functions
            .deadlines(String(message["machine"]), String(message["state"]))
            .map(([name, d]) => (d.kind === "delay" ? { name, delay: d.ms } : { name })),
        };
      case "deadlineAt":
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.deadlineAt(scope, this.records, String(message["name"]), access), (time) => ({
            time: time.toString(),
          })),
        );
      case "offers":
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.offers(scope, this.records, String(message["control"]), access), (payloads) => ({
            payloads: payloads.map((p) => p.encoded),
          })),
        );
      case "showInput": {
        const activity = message["activity"] as { keyword: string; key: string };
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.showInput(scope, this.records, activity, access), ({ encoded }) => ({
            input: encoded,
          })),
        );
      }
      case "items":
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.items(scope, this.records, access), (keys) => ({
            keys: keys.map((k) => ({ key: k.encoded, encodedKey: k.encodedKey })),
          })),
        );
      case "copyContext": {
        const machine = String(message["machine"]);
        const map = String(message["map"]);
        const shape = this.functions.node(machine, map)?.context ?? {};
        return { context: encode(shape, this.functions.copyContext(machine, map)) };
      }
      case "singleRecord": {
        return { record: this.functions.singleRecord(String(message["entity"])).encoded };
      }
      case "copyKey": {
        const machine = String(message["machine"]);
        const map = String(message["map"]);
        const { ref } = this.functions.chartOf(machine);
        const row = message["payload"] as Fields;
        const present = Object.fromEntries(
          Object.entries(this.functions.node(machine, map)?.key ?? {}).filter(([f]) => row[f] !== undefined),
        );
        // The payload arrives as JSON, so its key fields are decoded first.
        const fields = Object.fromEntries(Object.keys(present).map((f) => [f, row[f]]));
        return this.replied(decodeStrict({ kind: "mapKey", chart: ref, map }, present, fields), (decoded) =>
          decoded === undefined
            ? { key: null }
            : this.replied(this.functions.copyKey(machine, map, decoded), (key) => (key === undefined ? {} : { key })),
        );
      }
      case "close":
        return this.scoped(message, (scope, access) =>
          this.replied(this.functions.close(scope, this.records, access), ({ output, failed }) => ({
            output: encode(this.functions.chartOf(scope.machine).named.definition.output ?? {}, output),
            ...(failed === undefined ? {} : { failed }),
          })),
        );
      default:
        throw new Error(`tazuna-lean sent ${JSON.stringify(message)}`);
    }
  }
}
