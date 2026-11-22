import { join } from "node:path";
import { z } from "zod";
import { encoded } from "../data/collections.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { objectSchema } from "../data/jsonSchema.ts";
import type { Json, Shape } from "../data/values.ts";
import { stateAt, transitionAt } from "../dsl/chart.ts";
import type { Conditions } from "../dsl/conditions.ts";
import type { AnyCommand, AnyQuery, Automation, ChartSpec, Place } from "../dsl/definition.ts";
import type { AnyEntity } from "../dsl/entity.ts";
import type { Spec } from "../load/load.ts";
import { type ChartStructure, chartStructure, stateNamed, transitionRef } from "../spec/structure.ts";
import { type Arg, converted, type Defined, definedKey, type Typed } from "./expression.ts";
import type {
  ChartFns,
  Condition,
  Conditions as ConvertedConditions,
  Entry,
  Expr,
  Fn,
  Program,
  Site,
} from "./ir.generated.ts";
import { Locator } from "./located.ts";
import { Sources } from "./sources.ts";

/** A spec function that stays TS: the Program list it would join, whose condition it is (if any), and why. */
interface NotConverted {
  readonly callback: keyof Program;
  readonly definition: DefinitionRef;
  readonly name?: string;
  readonly reason: string;
}

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
  readonly shapes: readonly (Shape | undefined)[];
  /** Whether the callback takes the conditions only all together, as `firstFailing` runs them. */
  readonly whole: boolean;
  /** The binds slot whose values the conditions read as `bound`, which converts first. */
  readonly binds?: Slot;
  readonly typed: Typed;
}

const codecs = new WeakMap<Shape, boolean>();

/** Whether a value of `shape` holds a codec other than tazuna's time codecs, whose decoded value JSON does not show. */
function holdsCodec(shape: Shape): boolean {
  const known = codecs.get(shape);
  if (known !== undefined) return known;
  const holds = JSON.stringify(objectSchema(shape)).includes('"x-tazuna-codec"');
  codecs.set(shape, holds);
  return holds;
}

/** The one function of a definition that a callback evaluates, with its arguments and their schemas. */
interface FnSlot {
  readonly callback: FnCallback;
  readonly definition: DefinitionRef;
  readonly f: SpecFunction | undefined;
  readonly args: readonly Arg[];
  readonly shapes: readonly (Shape | undefined)[];
  /** The events that a decide's command lists. */
  readonly events?: readonly DefinitionRef[];
  /** The binds that the function reads as `bound`, which convert first. */
  readonly binds?: ConditionsCallback;
  readonly typed: Typed;
}

const sameRef = (a: DefinitionRef, b: DefinitionRef) => a.service === b.service && a.name === b.name;

const objectOf = (shape: Shape | undefined): z.ZodType | undefined =>
  shape === undefined ? undefined : z.object(shape);

/** The schemas of a service's records and of the arguments `args`, each an object of a shape. */
function typedOf(spec: Spec, service: string, args: Readonly<Record<string, Shape | undefined>>): Typed {
  const entities = (spec.services.get(service)?.definition.entities ?? {}) as Readonly<Record<string, AnyEntity>>;
  return {
    args: Object.fromEntries(Object.entries(args).map(([name, shape]) => [name, objectOf(shape)])),
    entities: Object.fromEntries(Object.entries(entities).map(([name, e]) => [name, z.object(e.fields)])),
  };
}

function fnSlotsOf(spec: Spec): FnSlot[] {
  const slots: FnSlot[] = [];
  for (const { service, name, definition: d } of spec.definitions) {
    const entities = Object.values(
      (spec.services.get(service)?.definition.entities ?? {}) as Readonly<Record<string, AnyEntity>>,
    ).map((e) => e.fields);
    if (d.kind === "query") {
      const query = d as AnyQuery;
      slots.push({
        callback: "resolve",
        definition: { service, name },
        f: query.resolve as SpecFunction | undefined,
        args: ["input", "records", "now"],
        shapes: [query.input, query.output, ...entities],
        typed: typedOf(spec, service, { input: query.input }),
      });
    }
    if (d.kind === "command") {
      const command = d as AnyCommand;
      slots.push({
        callback: "decide",
        definition: { service, name },
        f: command.decide as SpecFunction | undefined,
        args: ["input", "records", "now", "bound"],
        binds: "binding",
        typed: typedOf(spec, service, { input: command.input }),
        shapes: [command.input, ...command.emits.map((e) => e.payload), ...entities],
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
        typed: typedOf(spec, service, { payload: Object.values(automation.receives)[0]?.payload }),
        shapes: [
          ...Object.values(automation.receives).map((e) => e.payload),
          ...Object.values(automation.commands).map((c) => c.input),
          ...entities,
        ],
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
  readonly typed: Typed;
}

const scopeArgs: readonly Arg[] = ["context", "input", "shown", "key", "records", "active", "now", "held"];
const causeArgs: readonly Arg[] = [...scopeArgs, "payload", "output", "rejection"];
const assignArgs: readonly Arg[] = [...causeArgs, "createKey"];
const empty: Expr = { op: "obj", fields: [] };
const keywords = ["calls", "sends", "shows", "opens"] as const;

/**
 * The shapes of the values that a chart's functions read or make: its own schemas, those of the messages it takes and
 * sends, and the records of its service.
 */
function chartShapes(spec: Spec, service: string, chart: ChartSpec, structure: ChartStructure): (Shape | undefined)[] {
  const entities = (spec.services.get(service)?.definition.entities ?? {}) as Readonly<Record<string, AnyEntity>>;
  const states = structure.states.map((s) => stateAt(chart, s.path));
  return [
    chart.context,
    chart.input,
    chart.output,
    ...Object.values(chart.controls ?? {}).map((c) => c.payload),
    ...Object.values(chart.receives).map((e) => e.payload),
    ...Object.values(chart.queries ?? {}).flatMap((q) => [q.input, q.output]),
    ...Object.values(chart.commands).flatMap((c) => [c.input, c.output]),
    ...Object.values(chart.screens ?? {}).flatMap((s) => [s.input, s.output]),
    ...states.flatMap((s) => [s.held as Shape | undefined, s.context, s.type === "map" ? s.key : undefined]),
    ...Object.values(entities).map((e) => e.fields),
  ];
}

function chartSlotsOf(spec: Spec): ChartSlot[] {
  const slots: ChartSlot[] = [];
  for (const { service, name, definition: d } of spec.definitions) {
    if (d.kind !== "machine" && d.kind !== "screen") continue;
    const chartSpec = d as ChartSpec;
    const structure = chartStructure(spec.structure, service, name);
    if (structure === undefined) continue;
    if (chartShapes(spec, service, chartSpec, structure).some((shape) => shape !== undefined && holdsCodec(shape)))
      continue;
    const chart = { service, name };
    const contexts = [chartSpec.context, ...structure.states.map((st) => stateAt(chartSpec, st.path).context)];
    // A copy's field over the owner's of another schema could be either.
    const context = Object.fromEntries(
      [...new Set(contexts.flatMap((c) => Object.keys(c ?? {})))].flatMap((field) => {
        const schemas = new Set(contexts.flatMap((c) => (c?.[field] === undefined ? [] : [c[field]])));
        return schemas.size === 1 ? [[field, [...schemas][0]]] : [];
      }),
    ) as Shape;
    const typed = (state?: string | null): Typed => {
      const declaring = state === undefined || state === null ? undefined : stateNamed(structure, state);
      const held = declaring === undefined ? undefined : (stateAt(chartSpec, declaring.path).held as Shape | undefined);
      return typedOf(spec, service, { context, input: chartSpec.input, held });
    };
    const fns = (functions: Readonly<Record<string, unknown>> | undefined) =>
      Object.entries(functions ?? {}) as [string, SpecFunction][];
    slots.push(
      {
        chart,
        site: { kind: "invariants" },
        functions: fns(chartSpec.invariants),
        args: scopeArgs,
        whole: true,
        typed: typed(),
      },
      {
        chart,
        site: { kind: "initialContext" },
        functions: [["", chartSpec.initialContext]],
        args: ["input"],
        whole: true,
        typed: typed(),
      },
      {
        chart,
        site: { kind: "close" },
        functions: [["", chartSpec.resolve]],
        args: scopeArgs,
        whole: true,
        typed: typed(),
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
            typed: typed(state),
          });
    };
    offers(null, chartSpec.offers);
    const held = (
      entry: Entry,
      state: string,
      fills: Readonly<Record<string, unknown>> | undefined,
      args: readonly Arg[],
      declaring: string | null,
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
        typed: typed(declaring),
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
          typed: typed(t.source),
        },
        {
          chart,
          site: { kind: "transitionAssign", transition: ref },
          functions: fns(written.assign),
          args: assignArgs,
          whole: true,
          typed: typed(t.source),
        },
      );
      if (t.target !== null) held({ kind: "transition", transition: ref }, t.target, written.with, causeArgs, t.source);
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
          typed: typed(s.name),
        },
        {
          chart,
          site: { kind: "exitAssign", state: s.name },
          functions: fns(node.exit?.assign),
          args: assignArgs,
          whole: true,
          typed: typed(s.name),
        },
      );
      if (s.initial !== null) held({ kind: "initial", parent: s.name }, s.initial, node.initialWith, scopeArgs, s.name);
      for (const deadline of s.deadlines) {
        const at = node.after?.[deadline.name]?.at as SpecFunction | undefined;
        if (at !== undefined)
          slots.push({
            chart,
            site: { kind: "deadline", state: s.name, name: deadline.name },
            functions: [["", at]],
            args: scopeArgs,
            whole: true,
            typed: typed(s.name),
          });
      }
      if (node.type === "map")
        slots.push({
          chart,
          site: { kind: "items", state: s.name },
          functions: [["", node.items as SpecFunction]],
          args: scopeArgs,
          whole: true,
          typed: typed(s.name),
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
            typed: typed(s.name),
          });
    }
  }
  return slots;
}

function slotsOf(spec: Spec): Slot[] {
  const slots: Slot[] = [];
  const entityShapes = (service: string): Shape[] =>
    Object.values((spec.services.get(service)?.definition.entities ?? {}) as Readonly<Record<string, AnyEntity>>).map(
      (e) => e.fields,
    );
  for (const { service, name, definition: d } of spec.definitions) {
    const definition = { service, name };
    const entities = entityShapes(service);
    const typed = (args: Readonly<Record<string, Shape | undefined>>) => typedOf(spec, service, args);
    if (d.kind === "command" || d.kind === "query") {
      const target = d as AnyCommand | AnyQuery;
      const payloads = target.kind === "command" ? target.emits.map((e) => e.payload) : [];
      slots.push(
        {
          callback: "inputRequirement",
          definition,
          conditions: target.requires,
          args: ["input"],
          shapes: [target.input],
          whole: false,
          typed: typed({ input: target.input }),
        },
        {
          callback: "resultEnsures",
          definition,
          conditions: target.ensures,
          args: ["input", "output", "events", "records"],
          shapes: [target.input, target.output, ...payloads],
          whole: false,
          typed: typed({ input: target.input, output: target.output }),
        },
      );
      if (target.kind === "command") {
        const binds: Slot = {
          callback: "binding",
          definition,
          conditions: target.binds as Conditions<never>,
          args: ["input", "records", "now"],
          shapes: [target.input, ...entities],
          whole: true,
          typed: typed({ input: target.input }),
        };
        slots.push(
          binds,
          {
            callback: "requirement",
            definition,
            conditions: target.requires,
            args: ["input", "records", "now", "bound"],
            shapes: [target.input, ...entities],
            whole: false,
            typed: typed({ input: target.input }),
            binds,
          },
          {
            callback: "ensures",
            definition,
            conditions: target.ensures,
            args: ["input", "records", "bound"],
            shapes: [target.input, ...entities],
            whole: true,
            typed: typed({ input: target.input }),
            binds,
          },
        );
      } else
        slots.push({
          callback: "queryEnsures",
          definition,
          conditions: target.ensures,
          args: ["input", "output", "records"],
          shapes: [target.input, target.output, ...entities],
          whole: true,
          typed: typed({ input: target.input, output: target.output }),
        });
    }
    if (d.kind === "automation") {
      const automation = d as Automation;
      const payloads = Object.values(automation.receives).map((e) => e.payload);
      const binds: Slot = {
        callback: "automationBinding",
        definition,
        conditions: automation.binds as Conditions<never>,
        args: ["payload", "records", "now"],
        shapes: [...payloads, ...entities],
        whole: true,
        typed: typed({ payload: payloads[0] }),
      };
      slots.push(binds, {
        callback: "automationGuard",
        definition,
        conditions: automation.guard,
        args: ["payload", "records", "now", "bound"],
        shapes: [...payloads, ...entities],
        whole: false,
        typed: typed({ payload: payloads[0] }),
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
          shapes: [screen.input],
          whole: false,
          typed: typed({ input: screen.input }),
        },
        {
          callback: "closeEnsures",
          definition,
          conditions: screen.ensures,
          args: ["input", "output"],
          shapes: [screen.input, screen.output],
          whole: true,
          typed: typed({ input: screen.input, output: screen.output }),
        },
      );
    }
  }
  for (const [service, { definition }] of spec.services) {
    for (const [name, entity] of Object.entries(definition.entities as Readonly<Record<string, AnyEntity>>))
      slots.push({
        callback: "invariant",
        definition: { service, name },
        conditions: entity.invariants as Conditions<never>,
        args: ["record"],
        shapes: [entity.fields],
        whole: true,
        typed: typedOf(spec, service, { record: entity.fields }),
      });
    slots.push({
      callback: "serviceInvariant",
      definition: { service, name: service },
      conditions: definition.invariants as Conditions<never>,
      args: ["records"],
      shapes: entityShapes(service),
      whole: true,
      typed: typedOf(spec, service, {}),
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
   * its command lists; `defined` is what the spec defines outside its functions, which program() finds itself, and
   * `typed` the schemas of the arguments.
   */
  convert(
    f: SpecFunction,
    args: readonly Arg[],
    {
      events = [],
      defined = this.defined,
      typed,
    }: { readonly events?: readonly DefinitionRef[]; readonly defined?: Defined; readonly typed?: Typed } = {},
  ): Expr | { readonly unconverted: string } {
    const location = this.locator.located(f);
    const source = location === undefined ? undefined : this.sources.sourceAt(location);
    return source === undefined
      ? { unconverted: "has no source that the converter finds" }
      : converted(source, args, events, defined, typed);
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
      automationBinding: [],
      automationGuard: [],
    };
    const notConverted: NotConverted[] = [];
    const convertedBinds = new Set<Slot>();
    for (const slot of slotsOf(spec)) {
      const entries = Object.entries(slot.conditions ?? {}) as [string, SpecFunction][];
      const codec = slot.shapes.some((shape) => shape !== undefined && holdsCodec(shape));
      const binds = slot.binds === undefined || convertedBinds.has(slot.binds);
      const conditions: Condition[] = [];
      const failed: NotConverted[] = [];
      for (const [name, f] of entries) {
        const at = { callback: slot.callback, definition: slot.definition, name };
        const body = codec
          ? { unconverted: "receives a value of a codec" }
          : binds
            ? this.convert(f, slot.args, { typed: slot.typed })
            : { unconverted: "reads binds that stay TS" };
        if ("unconverted" in body) failed.push({ ...at, reason: body.unconverted });
        else conditions.push({ name, body });
      }
      notConverted.push(...failed);
      if (slot.whole ? failed.length === 0 : conditions.length > 0)
        lists[slot.callback].push({ definition: slot.definition, conditions });
      if (failed.length === 0) convertedBinds.add(slot);
    }
    const fns: Record<FnCallback, Fn[]> = { resolve: [], decide: [], react: [] };
    for (const slot of fnSlotsOf(spec)) {
      // An automation without input sends `{}`; a command without decide is an external service's.
      if (slot.f === undefined && slot.callback !== "react") continue;
      const { f } = slot;
      const codec = slot.shapes.some((shape) => shape !== undefined && holdsCodec(shape));
      const binds = slot.binds === undefined || lists[slot.binds].some((g) => sameRef(g.definition, slot.definition));
      const body = codec
        ? { unconverted: "receives a value of a codec" }
        : binds
          ? f === undefined
            ? empty
            : this.convert(f, slot.args, { events: slot.events ?? [], typed: slot.typed })
          : { unconverted: "reads binds that stay TS" };
      if ("unconverted" in body)
        notConverted.push({ callback: slot.callback, definition: slot.definition, reason: body.unconverted });
      else fns[slot.callback].push({ definition: slot.definition, body });
    }
    const chart: ChartFns[] = [];
    for (const slot of chartSlotsOf(spec)) {
      const functions: Condition[] = [];
      const failed: NotConverted[] = [];
      for (const [name, f] of slot.functions) {
        const body = f === undefined ? empty : this.convert(f, slot.args, { typed: slot.typed });
        if ("unconverted" in body)
          failed.push({
            callback: "chart",
            definition: slot.chart,
            name: `${slot.site.kind} ${name}`,
            reason: body.unconverted,
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
