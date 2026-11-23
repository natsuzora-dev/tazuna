import { join } from "node:path";
import { z } from "zod";
import { encoded } from "../data/collections.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Json, Shape } from "../data/values.ts";
import { stateAt, transitionAt } from "../dsl/chart.ts";
import type { Conditions } from "../dsl/conditions.ts";
import type { AnyCommand, AnyQuery, Automation, ChartSpec, Place } from "../dsl/definition.ts";
import { type AnyEntity, refTarget } from "../dsl/entity.ts";
import type { Spec } from "../load/load.ts";
import type {
  ChartFns,
  Condition,
  Conditions as ConvertedConditions,
  Entry,
  Expr,
  Fn,
  Program,
  Site,
} from "../spec/ir.generated.ts";
import { chartStructure, stateNamed, transitionRef } from "../spec/structure.ts";
import { type Arg, converted, type Defined, definedKey } from "./expression.ts";
import { type Location, Locator } from "./located.ts";
import { Sources } from "./sources.ts";

/**
 * A spec function outside the IR: the Program list it would join, whose condition it is (if any), why, and where its
 * source starts when the converter found it.
 */
export interface NotConverted {
  readonly callback: keyof Program;
  readonly definition: DefinitionRef;
  readonly name?: string;
  readonly reason: string;
  readonly location?: Location;
}

/** Why a function stays outside the IR, and where its source starts when the converter found it. */
type Unconverted = { readonly unconverted: string; readonly location?: Location };

/** The Program lists of named conditions, those of one function per definition, and the chart functions. */
type ConditionsCallback = Exclude<keyof Program, FnCallback | "chart">;
type FnCallback = "resolve" | "decide" | "react";

export interface Converted {
  readonly program: Program;
  readonly notConverted: readonly NotConverted[];
}

type SpecFunction = (args: never) => unknown;

/** The conditions of one definition that a callback evaluates, with the arguments and their schemas. */
interface Slot {
  readonly callback: ConditionsCallback;
  readonly definition: DefinitionRef;
  readonly conditions: Conditions<never> | undefined;
  readonly args: readonly Arg[];
  /** Whether the callback takes the conditions only all together, as `firstFailing` runs them. */
  readonly whole: boolean;
  /** The binds slot whose values the conditions read as `bound`, which converts first. */
  readonly binds?: Slot;
}

/** The one function of a definition that a callback evaluates, with its arguments and their schemas. */
interface FnSlot {
  readonly callback: FnCallback;
  readonly definition: DefinitionRef;
  readonly f: SpecFunction | undefined;
  readonly args: readonly Arg[];
  /** The events that a decide's command lists. */
  readonly events?: readonly DefinitionRef[];
  /** The binds that the function reads as `bound`, which convert first. */
  readonly binds?: ConditionsCallback;
}

/**
 * Whether the engine runs a function for the slot: a react always, since an automation without input sends `{}`, and a
 * resolve or decide only when written, since a command without decide is an external service's.
 */
const runsFn = (slot: FnSlot) => slot.f !== undefined || slot.callback === "react";

const located = (u: Unconverted) => (u.location === undefined ? {} : { location: u.location });

const sameRef = (a: DefinitionRef, b: DefinitionRef) => a.service === b.service && a.name === b.name;

/** The entity of each top-level `ref(entity)` field of the input of `d`, for the entities of its own service. */
function refsOf(spec: Spec, d: DefinitionRef): ReadonlyMap<string, string> {
  const definition = spec.definitions.find((x) => sameRef(x, d))?.definition;
  if (definition?.kind !== "command" && definition?.kind !== "query") return new Map();
  const entities = Object.entries(spec.services.get(d.service)?.definition.entities ?? {});
  return new Map(
    Object.entries((definition as AnyCommand | AnyQuery).input as Shape).flatMap(([field, schema]) => {
      if (schema instanceof z.ZodNullable || schema instanceof z.ZodDefault) return [];
      const target = refTarget(schema);
      const entity = entities.find(([, e]) => e === target)?.[0];
      return entity === undefined ? [] : [[field, entity] as const];
    }),
  );
}

function fnSlotsOf(spec: Spec): FnSlot[] {
  const slots: FnSlot[] = [];
  for (const { service, name, definition: d } of spec.definitions) {
    if (d.kind === "query") {
      const query = d as AnyQuery;
      slots.push({
        callback: "resolve",
        definition: { service, name },
        f: query.resolve as SpecFunction | undefined,
        args: ["input", "caller", "refs", "records", "now"],
      });
    }
    if (d.kind === "command") {
      const command = d as AnyCommand;
      slots.push({
        callback: "decide",
        definition: { service, name },
        f: command.decide as SpecFunction | undefined,
        args: ["input", "caller", "refs", "records", "now", "bound"],
        binds: "binding",
        events: command.emits.flatMap((e) => {
          const named = spec.names.get(e);
          return named === undefined ? [] : [{ service: named.service, name: named.name }];
        }),
      });
    }
    if (d.kind === "automation") {
      const automation = d as Automation;
      slots.push({
        callback: "react",
        definition: { service, name },
        f: automation.input,
        args: ["payload", "records", "now", "bound", "createKey"],
        binds: "automationBinding",
      });
    }
  }
  return slots;
}

/** The functions of one site of a chart, by name; a function that the chart leaves out is TS's `{}`, or none. */
interface ChartSlot {
  readonly chart: DefinitionRef;
  readonly site: Site;
  readonly functions: readonly (readonly [string, SpecFunction | undefined])[];
  readonly args: readonly Arg[];
  /** Whether the question reads every function of the site, as `firstFailing` or a held object does. */
  readonly whole: boolean;
}

const scopeArgs: readonly Arg[] = ["context", "input", "shown", "key", "records", "active", "now", "held"];
const causeArgs: readonly Arg[] = [...scopeArgs, "payload", "output", "rejection"];
const assignArgs: readonly Arg[] = [...causeArgs, "createKey"];
const empty: Expr = { op: "obj", fields: [] };
const keywords = ["calls", "sends", "shows", "opens"] as const;

function chartSlotsOf(spec: Spec): ChartSlot[] {
  const slots: ChartSlot[] = [];
  for (const { service, name, definition: d } of spec.definitions) {
    if (d.kind !== "machine" && d.kind !== "screen") continue;
    const chartSpec = d as ChartSpec;
    const structure = chartStructure(spec.structure, service, name);
    if (structure === undefined) continue;
    const chart = { service, name };
    const fns = (functions: Readonly<Record<string, unknown>> | undefined) =>
      Object.entries(functions ?? {}) as [string, SpecFunction][];
    slots.push(
      {
        chart,
        site: { kind: "invariants" },
        functions: fns(chartSpec.invariants),
        args: scopeArgs,
        whole: true,
      },
      {
        chart,
        site: { kind: "initialContext" },
        functions: [["", chartSpec.initialContext]],
        args: ["input"],
        whole: true,
      },
      {
        chart,
        site: { kind: "close" },
        functions: [["", chartSpec.resolve]],
        args: scopeArgs,
        whole: true,
      },
    );
    const offers = (state: string | null, offered: Readonly<Record<string, unknown>> | undefined) => {
      for (const [control, f] of Object.entries(offered ?? {}))
        if (typeof f === "function")
          slots.push({
            chart,
            site: { kind: "offers", state, control },
            functions: [["", f as SpecFunction]],
            args: scopeArgs,
            whole: true,
          });
    };
    offers(null, chartSpec.offers);
    const held = (
      entry: Entry,
      state: string,
      fills: Readonly<Record<string, unknown>> | undefined,
      args: readonly Arg[],
    ) => {
      const target = stateNamed(structure, state);
      if (target?.held === null || target === undefined) return;
      const shape = stateAt(chartSpec, target.path).held as Shape | undefined;
      const names = Object.keys(shape ?? {});
      if (names.some((n) => typeof fills?.[n] !== "function")) return;
      const functions = names.map((n) => [n, fills?.[n] as SpecFunction] as const);
      slots.push({
        chart,
        site: { kind: "held", entry, state },
        functions,
        args,
        whole: true,
      });
    };
    for (const t of [...structure.on, ...structure.states.flatMap((s) => s.transitions)]) {
      const ref = transitionRef(t);
      const written = transitionAt(chartSpec, structure, ref);
      slots.push(
        {
          chart,
          site: { kind: "guards", transition: ref },
          functions: fns(written.guard),
          args: causeArgs,
          whole: false,
        },
        {
          chart,
          site: { kind: "transitionAssign", transition: ref },
          functions: fns(written.assign),
          args: assignArgs,
          whole: true,
        },
      );
      if (t.target !== null) held({ kind: "transition", transition: ref }, t.target, written.with, causeArgs);
    }
    for (const s of structure.states) {
      const node = stateAt(chartSpec, s.path);
      slots.push(
        {
          chart,
          site: { kind: "entryAssign", state: s.name },
          functions: fns(node.entry?.assign),
          args: assignArgs,
          whole: true,
        },
        {
          chart,
          site: { kind: "exitAssign", state: s.name },
          functions: fns(node.exit?.assign),
          args: assignArgs,
          whole: true,
        },
      );
      if (s.initial !== null) held({ kind: "initial", parent: s.name }, s.initial, node.initialWith, scopeArgs);
      for (const deadline of s.deadlines) {
        const at = node.after?.[deadline.name]?.at as SpecFunction | undefined;
        if (at !== undefined)
          slots.push({
            chart,
            site: { kind: "deadline", state: s.name, name: deadline.name },
            functions: [["", at]],
            args: scopeArgs,
            whole: true,
          });
      }
      if (node.type === "map")
        slots.push({
          chart,
          site: { kind: "items", state: s.name },
          functions: [["", node.items as SpecFunction]],
          args: scopeArgs,
          whole: true,
        });
      offers(s.name, node.offers);
      for (const keyword of keywords)
        for (const [key, activity] of Object.entries(node[keyword] ?? {}))
          slots.push({
            chart,
            site: { kind: "input", state: s.name, keyword, key },
            functions: [["", (activity as { readonly input?: SpecFunction }).input]],
            args: keyword === "sends" ? [...scopeArgs, "createKey"] : scopeArgs,
            whole: true,
          });
    }
  }
  return slots;
}

function slotsOf(spec: Spec): Slot[] {
  const slots: Slot[] = [];
  for (const { service, name, definition: d } of spec.definitions) {
    const definition = { service, name };
    if (d.kind === "command" || d.kind === "query") {
      const target = d as AnyCommand | AnyQuery;
      slots.push(
        {
          callback: "inputRequirement",
          definition,
          conditions: target.requires,
          args: ["input"],
          whole: false,
        },
        {
          callback: "resultEnsures",
          definition,
          conditions: target.ensures,
          args: ["input", "output", "events", "records"],
          whole: false,
        },
      );
      if (target.kind === "command") {
        const binds: Slot = {
          callback: "binding",
          definition,
          conditions: target.binds as Conditions<never>,
          args: ["input", "caller", "refs", "records", "now"],
          whole: true,
        };
        slots.push(
          binds,
          {
            callback: "requirement",
            definition,
            conditions: target.requires,
            args: ["input", "caller", "refs", "records", "now", "bound"],
            whole: false,
            binds,
          },
          {
            callback: "ensures",
            definition,
            conditions: target.ensures,
            args: ["input", "caller", "records", "bound"],
            whole: true,
            binds,
          },
        );
      } else
        slots.push({
          callback: "queryEnsures",
          definition,
          conditions: target.ensures,
          args: ["input", "caller", "output", "records"],
          whole: true,
        });
    }
    if (d.kind === "automation") {
      const automation = d as Automation;
      const binds: Slot = {
        callback: "automationBinding",
        definition,
        conditions: automation.binds as Conditions<never>,
        args: ["payload", "records", "now"],
        whole: true,
      };
      slots.push(binds, {
        callback: "automationGuard",
        definition,
        conditions: automation.guard,
        args: ["payload", "records", "now", "bound"],
        whole: false,
        binds,
      });
    }
    if (d.kind === "screen") {
      const screen = d as ChartSpec;
      slots.push(
        {
          callback: "inputRequirement",
          definition,
          conditions: screen.requires,
          args: ["input"],
          whole: false,
        },
        {
          callback: "closeEnsures",
          definition,
          conditions: screen.ensures,
          args: ["input", "output"],
          whole: true,
        },
      );
    }
  }
  for (const [service, { definition }] of spec.services) {
    for (const [name, entity] of Object.entries(definition.entities as Readonly<Record<string, AnyEntity>>)) {
      const record = {
        definition: { service, name },
        args: ["record", "now"],
        whole: true,
      } as const;
      const responses = Object.entries(entity.responses);
      slots.push(
        { callback: "invariant", conditions: entity.invariants as Conditions<never>, ...record },
        {
          callback: "responseWhen",
          conditions: Object.fromEntries(responses.map(([n, r]) => [n, r.when])) as Conditions<never>,
          ...record,
        },
        {
          callback: "responseExpect",
          conditions: Object.fromEntries(responses.map(([n, r]) => [n, r.expect])) as Conditions<never>,
          ...record,
        },
      );
    }
    slots.push({
      callback: "serviceInvariant",
      definition: { service, name: service },
      conditions: definition.invariants as Conditions<never>,
      args: ["records", "now"],
      whole: true,
    });
  }
  return slots;
}

/**
 * Converts spec functions to IR. It reads each function's source in a tsgo process per tsconfig.json, found where the
 * running function starts; close() stops them.
 */
export class Converter {
  private readonly locator = new Locator();
  private readonly sources = new Sources();
  private defined: Defined = { constants: new Map(), entities: new Map() };

  close(): void {
    this.locator.close();
    this.sources.close();
  }

  /**
   * The IR of `f`, a spec function that receives `args`, or the reason that it stays TS. A decide's `events` are those
   * its command lists; `defined` is what the spec defines outside its functions, which program() finds itself; `refs`
   * names the entity of each top-level ref field of the input.
   */
  convert(
    f: SpecFunction,
    args: readonly Arg[],
    {
      events = [],
      defined = this.defined,
      refs = new Map(),
    }: {
      readonly events?: readonly DefinitionRef[];
      readonly defined?: Defined;
      readonly refs?: ReadonlyMap<string, string>;
    } = {},
  ): Expr | Unconverted {
    const location = this.locator.located(f);
    const source = location === undefined ? undefined : this.sources.sourceAt(location);
    if (source === undefined)
      return { unconverted: "has no source that the converter finds", ...(location && { location }) };
    const result = converted(source, args, events, defined, refs);
    return "unconverted" in result && location !== undefined ? { ...result, location } : result;
  }

  /** The IR of the spec functions of the callbacks that Lean evaluates, and those that stay TS. */
  program(spec: Spec): Converted {
    const key = ({ name, place }: { readonly name: string; readonly place: Place }) =>
      definedKey(join(spec.root, place.file), name);
    this.defined = {
      constants: new Map(
        spec.constants.flatMap((c) => {
          const json = encoded(c.definition.schema, c.definition.values);
          return "encoded" in json ? [[key(c), json.encoded as Readonly<Record<string, Json>>]] : [];
        }),
      ),
      entities: new Map(spec.definitions.filter((d) => d.definition.kind === "entity").map((d) => [key(d), d.name])),
    };
    const lists: Record<ConditionsCallback, ConvertedConditions[]> = {
      inputRequirement: [],
      resultEnsures: [],
      invariant: [],
      closeEnsures: [],
      binding: [],
      requirement: [],
      ensures: [],
      queryEnsures: [],
      serviceInvariant: [],
      responseWhen: [],
      responseExpect: [],
      automationBinding: [],
      automationGuard: [],
    };
    const notConverted: NotConverted[] = [];
    const convertedBinds = new Set<Slot>();
    for (const slot of slotsOf(spec)) {
      const entries = Object.entries(slot.conditions ?? {}) as [string, SpecFunction][];
      const binds = slot.binds === undefined || convertedBinds.has(slot.binds);
      const conditions: Condition[] = [];
      const failed: NotConverted[] = [];
      for (const [name, f] of entries) {
        const at = { callback: slot.callback, definition: slot.definition, name };
        const result = binds
          ? this.convert(f, slot.args, { refs: refsOf(spec, slot.definition) })
          : { unconverted: "reads binds that stay TS" };
        if ("unconverted" in result) failed.push({ ...at, reason: result.unconverted, ...located(result) });
        else conditions.push({ name, body: result });
      }
      notConverted.push(...failed);
      if (slot.whole ? failed.length === 0 : conditions.length > 0)
        lists[slot.callback].push({ definition: slot.definition, conditions });
      if (failed.length === 0) convertedBinds.add(slot);
    }
    const fns: Record<FnCallback, Fn[]> = { resolve: [], decide: [], react: [] };
    for (const slot of fnSlotsOf(spec)) {
      if (!runsFn(slot)) continue;
      const { f } = slot;
      const binds = slot.binds === undefined || lists[slot.binds].some((g) => sameRef(g.definition, slot.definition));
      const body: Expr | Unconverted = binds
        ? f === undefined
          ? empty
          : this.convert(f, slot.args, { events: slot.events ?? [], refs: refsOf(spec, slot.definition) })
        : { unconverted: "reads binds that stay TS" };
      if ("unconverted" in body)
        notConverted.push({
          callback: slot.callback,
          definition: slot.definition,
          reason: body.unconverted,
          ...located(body),
        });
      else fns[slot.callback].push({ definition: slot.definition, body });
    }
    const chart: ChartFns[] = [];
    for (const slot of chartSlotsOf(spec)) {
      const functions: Condition[] = [];
      const failed: NotConverted[] = [];
      for (const [name, f] of slot.functions) {
        const body = f === undefined ? empty : this.convert(f, slot.args);
        if ("unconverted" in body)
          failed.push({
            callback: "chart",
            definition: slot.chart,
            name: `${slot.site.kind} ${name}`,
            reason: body.unconverted,
            ...located(body),
          });
        else functions.push({ name, body });
      }
      notConverted.push(...failed);
      if (slot.whole ? failed.length === 0 : functions.length > 0)
        chart.push({ chart: slot.chart, site: slot.site, functions });
    }
    return { program: { ...lists, ...fns, chart }, notConverted };
  }
}
