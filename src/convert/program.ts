import type { DefinitionRef } from "../data/definitionRef.ts";
import { objectSchema } from "../data/jsonSchema.ts";
import type { Shape } from "../data/values.ts";
import type { Conditions } from "../dsl/conditions.ts";
import type { AnyCommand, AnyQuery, Automation, ChartSpec } from "../dsl/definition.ts";
import type { AnyEntity } from "../dsl/entity.ts";
import type { Spec } from "../load/load.ts";
import { type Arg, converted } from "./expression.ts";
import type { Condition, Conditions as ConvertedConditions, Expr, Fn, Program } from "./ir.generated.ts";
import { Locator } from "./located.ts";
import { Sources } from "./sources.ts";

/** A spec function that stays TS: the Program list it would join, whose condition it is (if any), and why. */
interface NotConverted {
  readonly callback: keyof Program;
  readonly definition: DefinitionRef;
  readonly name?: string;
  readonly reason: string;
}

/** The Program lists of named conditions, and those of one function per definition. */
type ConditionsCallback = Exclude<keyof Program, FnCallback>;
type FnCallback = "resolve";

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
        },
        {
          callback: "resultEnsures",
          definition,
          conditions: target.ensures,
          args: ["input", "output", "events"],
          shapes: [target.input, target.output, ...payloads],
          whole: false,
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
            binds,
          },
          {
            callback: "ensures",
            definition,
            conditions: target.ensures,
            args: ["input", "records", "bound"],
            shapes: [target.input, ...entities],
            whole: true,
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
      };
      slots.push(binds, {
        callback: "automationGuard",
        definition,
        conditions: automation.guard,
        args: ["payload", "records", "now", "bound"],
        shapes: [...payloads, ...entities],
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
          shapes: [screen.input],
          whole: false,
        },
        {
          callback: "closeEnsures",
          definition,
          conditions: screen.ensures,
          args: ["input", "output"],
          shapes: [screen.input, screen.output],
          whole: true,
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
      });
    slots.push({
      callback: "serviceInvariant",
      definition: { service, name: service },
      conditions: definition.invariants as Conditions<never>,
      args: ["records"],
      shapes: entityShapes(service),
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

  close(): void {
    this.locator.close();
    this.sources.close();
  }

  /** The IR of `f`, a spec function that receives `args`, or the reason that it stays TS. */
  convert(f: SpecFunction, args: readonly Arg[]): Expr | { readonly unconverted: string } {
    const location = this.locator.located(f);
    const source = location === undefined ? undefined : this.sources.sourceAt(location);
    return source === undefined ? { unconverted: "has no source that the converter finds" } : converted(source, args);
  }

  /** The IR of the spec functions of the callbacks that Lean evaluates, and those that stay TS. */
  program(spec: Spec): Converted {
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
            ? this.convert(f, slot.args)
            : { unconverted: "reads binds that stay TS" };
        if ("unconverted" in body) failed.push({ ...at, reason: body.unconverted });
        else conditions.push({ name, body });
      }
      notConverted.push(...failed);
      if (slot.whole ? failed.length === 0 : conditions.length > 0)
        lists[slot.callback].push({ definition: slot.definition, conditions });
      if (failed.length === 0) convertedBinds.add(slot);
    }
    const fns: Record<FnCallback, Fn[]> = { resolve: [] };
    for (const slot of fnSlotsOf(spec)) {
      if (slot.f === undefined) continue;
      const codec = slot.shapes.some((shape) => shape !== undefined && holdsCodec(shape));
      const body = codec ? { unconverted: "receives a value of a codec" } : this.convert(slot.f, slot.args);
      if ("unconverted" in body)
        notConverted.push({ callback: slot.callback, definition: slot.definition, reason: body.unconverted });
      else fns[slot.callback].push({ definition: slot.definition, body });
    }
    return { program: { ...lists, ...fns }, notConverted };
  }
}
