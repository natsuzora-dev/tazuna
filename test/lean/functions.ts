import type { z } from "zod";
import { enumerations, reversedBags } from "../../src/data/bag.ts";
import { Bag, comparable as comparableValue, Ref, Runs } from "../../src/data/canonical.ts";
import { bagged, fromJson, written } from "../../src/data/collections.ts";
import { type DefinitionRef, sameRef } from "../../src/data/definitionRef.ts";
import type { Trigger } from "../../src/data/transitionRef.generated.ts";
import {
  canonicalJson,
  type Fields,
  type Json,
  objectOf,
  plain,
  type Shape,
  strictObjectOf,
} from "../../src/data/values.ts";
import { thrown } from "../../src/data/violation.ts";
import type { AnyCommand, AnyEvent, AnyQuery, Automation, ServiceDefinition } from "../../src/dsl/definition.ts";
import type { AnyEntity } from "../../src/dsl/entity.ts";
import type { Spec } from "../../src/load/load.ts";
import { refOfDefinition } from "../../src/load/traceName.ts";
import type { Schema } from "../../src/service/basic.ts";
import {
  type Access,
  type Assignment,
  type CopyScope,
  type Edge,
  Failed,
  type Issue,
  type Keys,
  type NextKeys,
  type Scope,
} from "../../src/service/functions.ts";
import { chartOf, copyId, type InstanceId, mapOf, openedId, topId } from "../../src/service/instance.ts";
import type { Emit } from "../../src/service/message.ts";
import type { RecordSource } from "../../src/service/records.ts";
import { SpecFunctions } from "../../src/sim/spec/functions.ts";
import { transitionRef } from "../../src/spec/structure.ts";
import { keyPositionsOf } from "../../src/verify/compare.ts";
import type {
  Asked,
  Extra,
  Holder,
  Access as LeanAccess,
  Issue as LeanIssue,
  Keys as LeanKeys,
  Scope as LeanScope,
  Question,
  Replied,
  Reply,
} from "./protocol.generated.ts";

/** Writes a value that spec code made for `shape` as Lean holds it. */
const encode = (shape: Shape, value: unknown): Json => written(objectOf(shape), value);

/** The Keys of Lean's: the owner, if any, and what createKey returns next by entity. */
const keysOf = ({ owner, next }: LeanKeys): Keys => ({
  ...(owner === undefined ? {} : { owner }),
  next: Object.entries(next) as [string, NextKeys][],
});

/** The interned id of an id that Lean sent. */
const idOf = (id: InstanceId): InstanceId => {
  switch (id.kind) {
    case "top":
      return topId(id.chart);
    case "opened":
      return openedId(id.chart, idOf(id.opener), id.state, id.key);
    case "copy":
      return copyId(idOf(id.owner), id.map, canonicalJson(id.key));
  }
};

/** Returns a value of Lean's, which TS wrote of a checked value, as spec code receives it. */
const decodeValue = (schema: z.ZodType, value: unknown): unknown => bagged(schema, fromJson(schema, value));

const decode = (shape: Shape, value: unknown): Fields => decodeValue(objectOf(shape), value) as Fields;

/** Decodes `value` when it matches `shape` with no other fields, and returns undefined when it does not. */
function decodeStrict(schema: Schema, shape: Shape, value: unknown): Fields | undefined | Failed {
  try {
    const decoded = strictObjectOf(shape).safeParse(value);
    return decoded.success ? (bagged(strictObjectOf(shape), decoded.data) as Fields) : undefined;
  } catch (error) {
    return new Failed({ kind: "thrown", schema }, thrown(error));
  }
}

/** Decodes each field of `row` by its schema in `shape`; a field that `shape` lacks stays as it is. */
const decodeFields = (shape: Shape, row: Fields): Fields =>
  Object.fromEntries(
    Object.entries(row).map(([field, value]) => {
      const schema = shape[field];
      return [field, schema === undefined ? value : decodeValue(schema, value)];
    }),
  );

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
    return {
      type: "comparableValue",
      value: tagged(comparableValue(shape, asked.value, keyPositionsOf(this.spec)(shape))),
    };
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
        return value === undefined || schema === undefined ? value : decodeValue(schema, value);
      },
    });
    this.records = source({});
    this.before = source({ beforeEventWrite: true });
  }

  /** The payload of a decided event as its schema writes it, or as plain JSON for an event that the spec lacks. */
  private writtenPayload(e: Emit): Json {
    const defined = this.spec.definitions.some((d) => d.definition.kind === "event" && sameRef(d, e.event));
    return defined
      ? written(objectOf(this.functions.shape({ kind: "payload", event: e.event })), e.payload)
      : plain(e.payload);
  }

  private decoded(schema: Schema, value: unknown): Fields {
    return decode(this.functions.shape(schema), value);
  }

  /** Decodes the input of a request to the command or query `definition`. */
  private inputOf(definition: DefinitionRef, value: unknown): Fields {
    return this.decoded({ kind: "input", definition }, value);
  }

  /** Decodes the input of a request to the own command or query `name`. */
  private ownInputOf(name: string, value: unknown): Fields {
    return this.inputOf({ service: this.service, name }, value);
  }

  private issue(issue: Issue): LeanIssue {
    switch (issue.kind) {
      case "thrown":
        return issue.schema === undefined ? { kind: "thrown" } : { kind: "thrown", schema: issue.schema };
      case "schema":
        return { kind: "schema", schema: issue.schema };
      case "unheld":
      case "notOnly":
        return issue;
    }
  }

  /** Returns the reply of the value, or the Issue of a failed answer. */
  private replied<T>(value: T | Failed, reply: (value: T) => Replied): Replied {
    return value instanceof Failed ? { type: "issue", issue: this.issue(value.issue) } : reply(value);
  }

  private scopeOf(lean: LeanScope): Scope {
    const id = idOf(lean.id);
    const { named } = this.functions.chartOf(chartOf(id));
    const chart = named.definition;
    const context = decode(chart.context, lean.context);
    let copy: CopyScope | undefined;
    const map = mapOf(id);
    if (lean.copy !== null && map !== undefined) {
      const node = this.functions.node(chartOf(id), map);
      copy = { key: decode(node?.key ?? {}, lean.copy.key), context: decode(node?.context ?? {}, lean.copy.context) };
    }
    const shown = new Map<string, unknown>();
    for (const [slot, value] of Object.entries(lean.shown)) {
      const query = chart.queries?.[slot] as AnyQuery;
      shown.set(slot, value === null ? null : decode(query.output ?? {}, value));
    }
    const input = chart.kind === "screen" ? decode(chart.input ?? {}, lean.input) : {};
    const held = lean.state === null ? {} : decode(this.functions.node(chartOf(id), lean.state).held ?? {}, lean.held);
    return {
      id,
      state: lean.state,
      context,
      copy,
      active: new Set(lean.active),
      shown,
      input,
      held,
      now: Temporal.Instant.from(lean.now),
    };
  }

  /** Returns the extra of a transition with `trigger` as its expressions receive it, its payload or output decoded. */
  private extraOf(machine: string, trigger: Trigger | undefined, extra: Extra): Fields {
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
        return { payload: decode(this.functions.shape(schema), extra.payload) };
      }
      case "output": {
        const target = (
          keyword === "calls" ? chart.queries?.[key] : keyword === "opens" ? chart.screens?.[key] : chart.commands[key]
        ) as { readonly output?: Shape };
        const shape = keyword === "opens" ? (target.output ?? {}) : target.output;
        if (shape === undefined) return { output: extra.output };
        return { output: decode(shape, extra.output) };
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
    return { ...ask(this.scopeOf(lean), told), access };
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

  /** Returns the payload of the event that the automation receives, as spec code receives it. */
  private receivedOf(automation: string, payload: Json): Fields {
    const a = this.functions.definition<Automation>(["automation"], { service: this.service, name: automation });
    return decode(a.definition.receives.definition.payload, payload);
  }

  private answered(q: Question): Replied {
    const failed =
      (type: Exclude<Extract<Reply, { failed?: string }>["type"], "close">) =>
      (f: string | undefined): Replied =>
        ({ type, ...(f === undefined ? {} : { failed: f }) }) as Replied;
    const now = (q: { readonly now: string }) => Temporal.Instant.from(q.now);
    switch (q.type) {
      case "parse":
        return this.replied(this.functions.parse(q.schema, q.value), (parsed) => {
          if ("error" in parsed) return { type: "parse" };
          return { type: "parse", value: parsed.encoded as Json };
        });
      case "unordered":
        return this.replied(this.functions.unordered(q.schema, q.value), (value) => ({
          type: "unordered",
          value: value as Json,
        }));
      case "normalize": {
        const schema = q.schema;
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
        return this.replied(
          this.functions.binding(q.command, q.binding, this.ownInputOf(q.command, q.input), this.records, now(q)),
          (bound) => ({ type: "binding", bound }),
        );
      case "requirement":
        return this.replied(
          this.functions.requirement(q.command, q.condition, this.ownInputOf(q.command, q.input), this.records, now(q)),
          (holds) => ({ type: "requirement", holds }),
        );
      case "inputRequirement":
        return this.replied(
          this.functions.inputRequirement(q.target, q.condition, this.inputOf(q.target, q.input)),
          (holds) => ({ type: "inputRequirement", holds }),
        );
      case "decide":
        return this.replied(
          this.functions.decide(q.command, this.ownInputOf(q.command, q.input), this.records, now(q)),
          (decided) => ({
            type: "decide",
            groups: decided.map((g) => g.map((e) => ({ event: e.event, payload: this.writtenPayload(e) }))),
          }),
        );
      case "ensures":
        return this.replied(
          this.functions.ensures(q.command, this.ownInputOf(q.command, q.input), this.before, this.records, now(q)),
          failed("ensures"),
        );
      case "queryEnsures":
        return this.replied(
          this.functions.queryEnsures(
            q.query,
            this.ownInputOf(q.query, q.input),
            this.decoded({ kind: "output", definition: { service: this.service, name: q.query } }, q.output),
            this.records,
          ),
          failed("queryEnsures"),
        );
      case "resultEnsures": {
        const input = this.inputOf(q.target, q.input);
        const target = this.functions.definition<AnyCommand | AnyQuery>(["command", "query"], q.target).definition;
        const output =
          target.output === undefined ? undefined : this.decoded({ kind: "output", definition: q.target }, q.output);
        const events: Emit[] = q.events.map((e) => ({
          event: e.event,
          payload: this.decoded({ kind: "payload", event: e.event }, e.payload),
        }));
        return this.replied(this.functions.resultEnsures(q.target, q.condition, input, output, events), (ensured) => ({
          type: "resultEnsures",
          ensured,
        }));
      }
      case "invariant": {
        const fields = (this.owner.entities[q.entity] as AnyEntity).fields as Shape;
        return this.replied(
          this.functions.invariant(q.entity, decodeFields(fields, q.record as Fields)),
          failed("invariant"),
        );
      }
      case "serviceInvariant":
        return this.replied(this.functions.serviceInvariant(this.records), failed("serviceInvariant"));
      case "chartInvariant":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.chartInvariant(scope, this.records, access), failed("chartInvariant")),
        );
      case "resolve":
        // Lean's Value has no undefined, so an output that author code left undefined is sent as null.
        return this.replied(
          this.functions.resolve(q.query, this.ownInputOf(q.query, q.input), this.records, now(q)),
          (output) => ({
            type: "resolve",
            output: written(
              objectOf(this.functions.shape({ kind: "output", definition: { service: this.service, name: q.query } })),
              output,
            ),
          }),
        );
      case "automationBinding":
        return this.replied(
          this.functions.automationBinding(
            q.automation,
            q.binding,
            this.receivedOf(q.automation, q.payload),
            this.records,
            now(q),
          ),
          (bound) => ({ type: "automationBinding", bound }),
        );
      case "automationGuard":
        return this.replied(
          this.functions.automationGuard(
            q.automation,
            q.condition,
            this.receivedOf(q.automation, q.payload),
            this.records,
            now(q),
          ),
          (holds) => ({ type: "automationGuard", holds }),
        );
      case "react":
        return this.replied(
          this.functions.react(
            q.automation,
            this.receivedOf(q.automation, q.payload),
            this.records,
            now(q),
            keysOf(q.keys),
          ),
          ({ written, created }) => ({ type: "react", input: written, created: [...created] }),
        );
      case "comparable":
        return this.replied(this.functions.comparable(q.query, q.answer), (compared) => ({
          type: "comparable",
          value: canonicalJson(compared),
        }));
      case "initialContext": {
        const chart = this.functions.chartOf(q.machine).named.definition;
        return this.replied(
          this.functions.initialContext(q.machine, decode(chart.input ?? {}, q.input)),
          (context) => ({
            type: "initialContext",
            context: encode(chart.context, context),
          }),
        );
      }
      case "guard":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(
            this.functions.guard(
              scope,
              this.records,
              transitionRef(q.transition),
              q.condition,
              this.extraOf(chartOf(scope.id), q.transition.trigger, q.extra),
              access,
            ),
            (holds) => ({ type: "guard", holds }),
          ),
        );
      case "assign": {
        const at = q.assignment;
        const assignment: Assignment =
          at.kind === "transition" ? { kind: "transition", transition: transitionRef(at.transition) } : at;
        const trigger = at.kind === "transition" ? at.transition.trigger : undefined;
        return this.scoped(q.scope, (scope, access) => {
          const extra = this.extraOf(chartOf(scope.id), trigger, q.extra);
          return this.replied(
            this.functions.assign(scope, this.records, assignment, extra, keysOf(q.keys), access),
            ({ context, copyContext, created }) => {
              const { copy } = scope;
              const chart = this.functions.chartOf(chartOf(scope.id)).named.definition;
              const map = mapOf(scope.id);
              const shape = map === undefined ? {} : (this.functions.node(chartOf(scope.id), map).context ?? {});
              return {
                type: "assign",
                context: encode(chart.context, context),
                ...(copy === undefined ? {} : { copy: encode(shape, copyContext ?? copy.context) }),
                created: [...created],
              };
            },
          );
        });
      }
      case "input":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(
            this.functions.input(scope, this.records, q.activity, keysOf(q.keys), access),
            ({ written, created }) => ({ type: "input", input: written, created: [...created] }),
          ),
        );
      case "held": {
        const at = q.edge;
        const edge: Edge =
          at.kind === "transition" ? { kind: "transition", transition: transitionRef(at.transition) } : at;
        const trigger = at.kind === "transition" ? at.transition.trigger : undefined;
        return this.scoped(q.scope, (scope, access) => {
          const machine = chartOf(scope.id);
          return this.replied(
            this.functions.held(scope, this.records, q.state, edge, this.extraOf(machine, trigger, q.extra), access),
            (fields) => ({ type: "held", held: encode(this.functions.node(machine, q.state).held ?? {}, fields) }),
          );
        });
      }
      case "deadlines":
        return { type: "deadlines", names: [...this.functions.deadlines(q.machine, q.state)] };
      case "deadlineTime":
        return this.scoped(q.scope, (scope, access) =>
          this.replied(this.functions.deadlineTime(scope, this.records, q.name, access), (time) =>
            time === undefined ? { type: "deadlineTime" } : { type: "deadlineTime", time },
          ),
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
            keys: keys.map((k) => ({ key: k.encoded as Json, canonical: JSON.parse(k.encodedKey) as Json })),
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
                key === undefined
                  ? { type: "copyKey" }
                  : { type: "copyKey", key: key === null ? null : (JSON.parse(key) as Json) },
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
