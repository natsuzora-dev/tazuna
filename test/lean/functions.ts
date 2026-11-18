import { enumerations, reversedBags } from "../../src/data/bag.ts";
import { Bag, comparable as comparableValue, Ref, Runs } from "../../src/data/canonical.ts";
import { bagged, sorted } from "../../src/data/collections.ts";
import type { Trigger } from "../../src/data/transitionRef.generated.ts";
import {
  canonicalJson,
  encode as encodeArrays,
  type Fields,
  type Json,
  objectOf,
  type Shape,
  strictObjectOf,
} from "../../src/data/values.ts";
import { thrown } from "../../src/data/violation.ts";
import type { AnyCommand, AnyEvent, AnyQuery, Automation, Named, ServiceDefinition } from "../../src/dsl/definition.ts";
import type { AnyEntity } from "../../src/dsl/entity.ts";
import type { Spec } from "../../src/load/load.ts";
import { refOfDefinition } from "../../src/load/traceName.ts";
import type { Schema } from "../../src/service/basic.ts";
import {
  type Access,
  type Assignment,
  type CopyScope,
  Failed,
  type Issue,
  type Keys,
  type NextKeys,
  type Scope,
} from "../../src/service/functions.ts";
import { chartOf, copyId, type InstanceId, mapOf, topId } from "../../src/service/instance.ts";
import type { Emit } from "../../src/service/message.ts";
import type { RecordSource } from "../../src/service/records.ts";
import { SpecFunctions } from "../../src/sim/spec/functions.ts";
import { traceNameOfRef, transitionRef } from "../../src/spec/structure.ts";
import { refEntityOf } from "../../src/verify/compare.ts";
import type {
  Asked,
  Extra,
  Holder,
  Access as LeanAccess,
  Issue as LeanIssue,
  Keys as LeanKeys,
  Schema as LeanSchema,
  Scope as LeanScope,
  Question,
  Replied,
  Reply,
} from "./protocol.generated.ts";

/** Encodes a value as spec code receives it, whose bags, sets and sortedBy arrays are Bags and Runs. */
const encode = (shape: Shape, value: unknown): Json => encodeArrays(shape, sorted(objectOf(shape), value)) as Json;

/** The Keys of Lean's: the owner, if any, and what createKey returns next by entity. */
const keysOf = ({ owner, next }: LeanKeys): Keys => ({
  ...(owner === undefined ? {} : { owner }),
  next: Object.entries(next) as [string, NextKeys][],
});

/** The interned id of an id that Lean sent. */
const idOf = (id: InstanceId): InstanceId =>
  id.kind === "top" ? topId(id.chart, id.serial) : copyId(idOf(id.owner), id.map, id.key);

const json = (value: unknown): Json | undefined =>
  value === undefined ? undefined : (JSON.parse(JSON.stringify(value)) as Json);

/**
 * Returns `f()`, which decodes a value of Lean's message, or, when it throws, a `thrown` failure of `schema`, as in
 * src/sim/spec.
 */
function decoding<T>(f: () => T, schema?: Schema): T | Failed {
  try {
    return f();
  } catch (error) {
    return new Failed(schema === undefined ? { kind: "thrown" } : { kind: "thrown", schema }, thrown(error));
  }
}

/** Decodes `value`, an encoded value of `shape`, as spec code receives it. */
function decode(schema: Schema, shape: Shape, value: unknown): Fields | Failed {
  return decoding(() => bagged(objectOf(shape), objectOf(shape).parse(value)) as Fields, schema);
}

/** Decodes `value` when it matches `shape` with no other fields, and returns undefined when it does not. */
function decodeStrict(schema: Schema, shape: Shape, value: unknown): Fields | undefined | Failed {
  const decoded = decoding(() => strictObjectOf(shape).safeParse(value), schema);
  if (decoded instanceof Failed) return decoded;
  return decoded.success ? (bagged(strictObjectOf(shape), decoded.data) as Fields) : undefined;
}

/**
 * Decodes each field of `row` by its schema in `shape`. A field that fails it, or that `shape` lacks, stays as it is.
 */
function decodeFields(shape: Shape, row: Fields): Fields | Failed {
  return decoding(() =>
    Object.fromEntries(
      Object.entries(row).map(([field, value]) => {
        const schema = shape[field];
        const decoded = schema?.safeParse(value);
        return [field, schema !== undefined && decoded?.success === true ? bagged(schema, decoded.data) : value];
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
  answer(asked: Asked): Replied;
}

/** Tags each value with its shape for Lean. Objects become [name, value] pairs to keep their key order. */
export function tagged(value: unknown): Json {
  if (value instanceof Ref) return { ref: [value.entity, value.value] };
  if (value instanceof Bag) return { bag: value.items.map(tagged) };
  if (value instanceof Runs) return { runs: value.runs.map(tagged) };
  if (Array.isArray(value)) return { arr: value.map(tagged) };
  if (value !== null && typeof value === "object")
    return {
      obj: Object.entries(value)
        .filter(([, v]) => v !== undefined)
        .map(([k, v]) => [k, tagged(v)]),
    };
  return { leaf: value as Json };
}

export class VerifyFunctions implements Answering {
  private readonly spec: Spec;
  constructor(spec: Spec) {
    this.spec = spec;
  }

  answer(asked: Asked): Replied {
    if (asked.type !== "comparableValue") throw new Error(`verify asks no ${asked.type}`);
    const { kind, definition: ref, part } = asked;
    const found = this.spec.definitions.find(
      (d) => d.service === ref.service && d.name === ref.name && d.definition.kind === kind,
    )?.definition;
    if (found === undefined) throw new Error(`no ${kind} ${ref.service}.${ref.name}`);
    const shape = ((): Shape | undefined => {
      switch (part.kind) {
        case "input":
          return (found as AnyCommand | AnyQuery).input;
        case "output":
          return (found as AnyCommand | AnyQuery).output;
        case "payload":
          return (found as AnyEvent).payload;
        default:
          return (found as { controls?: Record<string, { payload?: Shape }> }).controls?.[part.name]?.payload;
      }
    })();
    return { type: "comparableValue", value: tagged(comparableValue(shape, asked.value, refEntityOf(this.spec))) };
  }
}

/**
 * Carries Lean's questions to the spec functions of src/sim/spec: decodes Lean's values, answers with the same SpecFunctions
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
        return value === undefined || schema === undefined ? value : bagged(schema, schema.parse(value));
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
      case "record":
        return { kind: "record", entity: schema.entity.name };
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
      case "record":
        return { kind: "record", entity: { service: this.service, name: lean.entity } };
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

  private issue(issue: Issue): LeanIssue {
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
  private replied<T>(value: T | Failed, reply: (value: T) => Replied): Replied {
    return value instanceof Failed ? { type: "issue", issue: this.issue(value.issue) } : reply(value);
  }

  private scopeOf(lean: LeanScope): Scope | Failed {
    const id = idOf(lean.id);
    const { named, ref } = this.functions.chartOf(chartOf(id));
    const chart = named.definition;
    const context = decode({ kind: "context", chart: ref }, chart.context, lean.context);
    if (context instanceof Failed) return context;
    let copy: CopyScope | undefined;
    const map = mapOf(id);
    if (lean.copy !== null && map !== undefined) {
      const node = this.functions.node(chartOf(id), map);
      const key = decode({ kind: "mapKey", chart: ref, map }, node?.key ?? {}, lean.copy.key);
      if (key instanceof Failed) return key;
      const own = decode({ kind: "mapContext", chart: ref, map }, node?.context ?? {}, lean.copy.context);
      if (own instanceof Failed) return own;
      copy = { key, context: own };
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
      id,
      state: lean.state,
      context,
      copy,
      active: new Set(lean.active),
      shown,
      input,
      now: Temporal.Instant.from(lean.now),
    };
  }

  /** Returns the extra of a transition with `trigger` as its expressions receive it, its payload or output decoded. */
  private extraOf(machine: string, trigger: Trigger | undefined, extra: Extra): Fields | Failed {
    const { named, ref } = this.functions.chartOf(machine);
    const chart = named.definition;
    const keyword = trigger?.type;
    const key = trigger !== undefined && "key" in trigger ? trigger.key : "";
    switch (extra.kind) {
      case "none":
        return {};
      case "rejection":
        return { rejection: { kind: extra.rejection.kind } };
      case "payload": {
        const schema: Schema =
          chart.controls?.[key] === undefined
            ? { kind: "payload", event: refOfDefinition(this.spec, chart.receives[key]) }
            : { kind: "control", screen: ref, control: key };
        const payload = decode(schema, this.functions.shape(schema), extra.payload);
        return payload instanceof Failed ? payload : { payload };
      }
      case "output": {
        const target = (
          keyword === "calls" ? chart.queries?.[key] : keyword === "opens" ? chart.screens?.[key] : chart.commands[key]
        ) as { readonly output?: Shape };
        const shape = keyword === "opens" ? (target.output ?? {}) : target.output;
        if (shape === undefined) return { output: extra.output };
        const output = decode({ kind: "output", definition: refOfDefinition(this.spec, target) }, shape, extra.output);
        return output instanceof Failed ? output : { output };
      }
    }
  }

  /** Returns the reply of a question about `scope`, with what its expressions read and assigned. */
  private scoped(lean: LeanScope, ask: (scope: Scope, access: Access) => Replied): Replied {
    const context: [Holder, string][] = [];
    const active: [Holder, string][] = [];
    const assigned: [Holder, string][] = [];
    const shown: string[] = [];
    const access: LeanAccess = { context, active, assigned, shown };
    const told: Access = {
      context: (holder, name) => context.push([holder, name]),
      active: (holder, name) => active.push([holder, name]),
      assigned: (holder, name) => assigned.push([holder, name]),
      shown: (slot) => shown.push(slot),
      now: () => {},
    };
    return { ...this.replied(this.scopeOf(lean), (scope) => ask(scope, told)), access };
  }

  /**
   * Answers Lean's question, with every Bag in reverse order when it has `reversed`, and tells whether a Bag of two or
   * more values ran a callback while answering, as Lean's lastEnumerated asks.
   */
  answer(asked: Asked): Replied {
    const before = enumerations();
    const reply = asked.reversed === true ? reversedBags(() => this.answered(asked)) : this.answered(asked);
    return enumerations() === before ? reply : { ...reply, enumerated: true };
  }

  private answered(q: Question): Replied {
    const failed =
      (type: Exclude<Extract<Reply, { failed?: string }>["type"], "close">) =>
      (f: string | undefined): Replied =>
        ({ type, ...(f === undefined ? {} : { failed: f }) }) as Replied;
    const now = (q: { readonly now: string }) => Temporal.Instant.from(q.now);
    switch (q.type) {
      case "parse": {
        const schema = this.schemaOf(q.schema);
        return this.replied(this.functions.parse(schema, q.value), (parsed) =>
          "error" in parsed ? { type: "parse" } : { type: "parse", value: parsed.encoded as Json },
        );
      }
      case "unordered": {
        const schema = this.schemaOf(q.schema);
        return this.replied(this.functions.unordered(schema, q.value), (value) => ({
          type: "unordered",
          value: value as Json,
        }));
      }
      case "normalize": {
        const schema = this.schemaOf(q.schema);
        // The value arrives as JSON, so it is decoded first.
        return this.replied(decodeStrict(schema, this.functions.shape(schema), q.value), (decoded) =>
          decoded === undefined
            ? { type: "normalize" }
            : this.replied(this.functions.normalize(schema, decoded), (normalized) =>
                "error" in normalized
                  ? { type: "normalize" }
                  : { type: "normalize", value: normalized.encoded as Json },
              ),
        );
      }
      case "binding":
        return this.replied(this.inputOf(q.command, q.input), (input) =>
          this.replied(this.functions.binding(q.command, q.binding, input, this.records, now(q)), (bound) => ({
            type: "binding",
            bound,
          })),
        );
      case "requirement":
        return this.replied(this.inputOf(q.command, q.input), (input) =>
          this.replied(this.functions.requirement(q.command, q.condition, input, this.records, now(q)), (holds) => ({
            type: "requirement",
            holds,
          })),
        );
      case "inputRequirement":
        return this.replied(this.inputOf(q.target, q.input), (input) =>
          this.replied(this.functions.inputRequirement(q.target, q.condition, input), (holds) => ({
            type: "inputRequirement",
            holds,
          })),
        );
      case "decide":
        return this.replied(this.inputOf(q.command, q.input), (input) =>
          this.replied(this.functions.decide(q.command, input, this.records, now(q)), (decided) => ({
            type: "decide",
            groups: decided.map((g) => g.map((e) => ({ event: e.event, payload: json(e.payload) ?? null }))),
          })),
        );
      case "ensures":
        return this.replied(this.inputOf(q.command, q.input), (input) =>
          this.replied(this.functions.ensures(q.command, input, this.before, this.records, now(q)), failed("ensures")),
        );
      case "queryEnsures":
        return this.replied(this.inputOf(q.query, q.input), (input) =>
          this.replied(this.decoded({ kind: "output", definition: q.query }, q.output), (output) =>
            this.replied(this.functions.queryEnsures(q.query, input, output, this.records), failed("queryEnsures")),
          ),
        );
      case "resultEnsures": {
        const reply = failed("resultEnsures");
        const input = this.inputOf(q.target, q.input);
        if (input instanceof Failed) return this.replied(input, reply);
        const target = this.functions.definition<AnyCommand | AnyQuery>(["command", "query"], q.target).definition;
        const output =
          target.output === undefined ? undefined : this.decoded({ kind: "output", definition: q.target }, q.output);
        if (output instanceof Failed) return this.replied(output, reply);
        const events: Emit[] = [];
        for (const e of q.events) {
          const payload = this.decoded({ kind: "payload", event: e.event }, e.payload);
          if (payload instanceof Failed) return this.replied(payload, reply);
          events.push({ event: e.event, payload });
        }
        return this.replied(this.functions.resultEnsures(q.target, input, output, events), reply);
      }
      case "invariant": {
        const fields = (this.owner.entities[q.entity] as AnyEntity).fields as Shape;
        return this.replied(decodeFields(fields, q.record as Fields), (record) =>
          this.replied(this.functions.invariant(q.entity, record), failed("invariant")),
        );
      }
      case "serviceInvariant":
        return this.replied(this.functions.serviceInvariant(this.records), failed("serviceInvariant"));
      case "chartInvariant":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.chartInvariant(scope, this.records, access), failed("chartInvariant")),
        );
      case "resolve":
        return this.replied(this.inputOf(q.query, q.input), (input) =>
          // Lean's Value has no undefined, so an output that author code left undefined is sent as null.
          this.replied(this.functions.resolve(q.query, input, this.records, now(q)), (output) => ({
            type: "resolve",
            output: json(output) ?? null,
          })),
        );
      case "react": {
        const a = this.functions.definition<Automation>(["automation"], q.automation).definition;
        const event = this.spec.names.get(Object.values(a.receives)[0]) as Named<AnyEvent>;
        const schema: Schema = { kind: "payload", event: { service: event.service, name: event.name } };
        return this.replied(decode(schema, event.definition.payload, q.payload), (payload) =>
          this.replied(
            this.functions.react(q.automation, payload, this.records, now(q), keysOf(q.keys)),
            ({ written, created }) =>
              written === undefined
                ? { type: "react", created: [...created] }
                : { type: "react", input: written, created: [...created] },
          ),
        );
      }
      case "comparable":
        return this.replied(this.functions.comparable(q.query, q.answer), (compared) => ({
          type: "comparable",
          value: canonicalJson(compared),
        }));
      case "initialContext": {
        const { named, ref } = this.functions.chartOf(q.machine);
        const chart = named.definition;
        const input = decode({ kind: "input", definition: ref }, chart.input ?? {}, q.input);
        return this.replied(input, (decoded) =>
          this.replied(this.functions.initialContext(q.machine, decoded), (context) => ({
            type: "initialContext",
            context: encode(chart.context, context),
          })),
        );
      }
      case "guard":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.extraOf(chartOf(scope.id), q.transition.trigger, q.extra), (extra) =>
            this.replied(
              this.functions.guard(scope, this.records, transitionRef(q.transition), extra, access),
              (passes) => ({ type: "guard", passes }),
            ),
          ),
        );
      case "assign": {
        const at = q.assignment;
        const assignment: Assignment =
          at.kind === "transition" ? { kind: "transition", transition: transitionRef(at.transition) } : at;
        const trigger = at.kind === "transition" ? at.transition.trigger : undefined;
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.extraOf(chartOf(scope.id), trigger, q.extra), (extra) =>
            this.replied(
              this.functions.assign(scope, this.records, assignment, extra, keysOf(q.keys), access),
              ({ context, copyContext, created }) => {
                const { copy } = scope;
                const chart = this.functions.chartOf(chartOf(scope.id)).named.definition;
                const map = mapOf(scope.id);
                const shape = map === undefined ? {} : (this.functions.node(chartOf(scope.id), map)?.context ?? {});
                return {
                  type: "assign",
                  context: encode(chart.context, context),
                  ...(copy === undefined ? {} : { copy: encode(shape, copyContext ?? copy.context) }),
                  created: [...created],
                };
              },
            ),
          ),
        );
      }
      case "input":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(
            this.functions.input(scope, this.records, q.activity, keysOf(q.keys), access),
            ({ written, created }) => ({ type: "input", input: written, created: [...created] }),
          ),
        );
      case "holds":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.holds(scope, this.records, access), () => ({ type: "holds" })),
        );
      case "deadlines":
        return {
          type: "deadlines",
          deadlines: this.functions
            .deadlines(q.machine, q.state)
            .map(([name, d]) => (d.kind === "delay" ? { name, delay: d.ms } : { name })),
        };
      case "deadlineAt":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.deadlineAt(scope, this.records, q.name, access), (time) => ({
            type: "deadlineAt",
            time: time.toString(),
          })),
        );
      case "offers":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.offers(scope, this.records, q.control, access), (payloads) => ({
            type: "offers",
            payloads: payloads.map((p) => p.encoded as Json),
          })),
        );
      case "showInput":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.showInput(scope, this.records, q.activity, access), (input) => ({
            type: "showInput",
            input,
          })),
        );
      case "items":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.items(scope, this.records, access), (keys) => ({
            type: "items",
            keys: keys.map((k) => ({ key: k.encoded as Json, encodedKey: k.encodedKey })),
          })),
        );
      case "copyContext": {
        const shape = this.functions.node(q.machine, q.map)?.context ?? {};
        return { type: "copyContext", context: encode(shape, this.functions.copyContext(q.machine, q.map)) };
      }
      case "singleRecord":
        return { type: "singleRecord", record: this.functions.singleRecord(q.entity).encoded as Json };
      case "copyKey": {
        const { ref } = this.functions.chartOf(q.machine);
        const row = q.payload as Fields;
        const present = Object.fromEntries(
          Object.entries(this.functions.node(q.machine, q.map)?.key ?? {}).filter(([f]) => row[f] !== undefined),
        );
        // The payload arrives as JSON, so its key fields are decoded first.
        const fields = Object.fromEntries(Object.keys(present).map((f) => [f, row[f]]));
        return this.replied(decodeStrict({ kind: "mapKey", chart: ref, map: q.map }, present, fields), (decoded) =>
          decoded === undefined
            ? { type: "copyKey", key: null }
            : this.replied(this.functions.copyKey(q.machine, q.map, decoded), (key) =>
                key === undefined ? { type: "copyKey" } : { type: "copyKey", key },
              ),
        );
      }
      case "close":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.close(scope, this.records, access), ({ output, failed }) => ({
            type: "close",
            output: encode(this.functions.chartOf(chartOf(scope.id)).named.definition.output ?? {}, output),
            ...(failed === undefined ? {} : { failed }),
          })),
        );
      case "comparableValue":
      case "served":
        throw new Error(`tazuna-lean sent ${JSON.stringify(q)} to the spec functions`);
    }
  }
}

/** Carries each question of a simulation to the RunFunctions of the service that the question names. */
export class SimFunctions implements Answering {
  private readonly services = new Map<string, RunFunctions>();
  private readonly spec: Spec;
  private readonly read: ReadRecord;

  constructor(spec: Spec, read: ReadRecord) {
    this.spec = spec;
    this.read = read;
  }

  answer(asked: Asked): Replied {
    const { service, ...question } = asked;
    if (service === undefined) throw new Error(`tazuna-lean asked ${asked.type} about no service`);
    const known = this.services.get(service) ?? new RunFunctions(this.spec, service, this.read);
    this.services.set(service, known);
    return known.answer(question);
  }
}
