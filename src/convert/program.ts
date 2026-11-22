import type { DefinitionRef } from "../data/definitionRef.ts";
import { objectSchema } from "../data/jsonSchema.ts";
import type { Shape } from "../data/values.ts";
import type { Conditions } from "../dsl/conditions.ts";
import type { AnyCommand, AnyQuery, ChartSpec } from "../dsl/definition.ts";
import type { AnyEntity } from "../dsl/entity.ts";
import type { Spec } from "../load/load.ts";
import { type Arg, converted } from "./expression.ts";
import type { Condition, Expr, Program } from "./ir.generated.ts";
import { Locator } from "./located.ts";
import { Sources } from "./sources.ts";

/** A spec function that stays TS: the Program list it would join, whose condition it is, and why. */
interface NotConverted {
  readonly callback: keyof Program;
  readonly definition: DefinitionRef;
  readonly name: string;
  readonly reason: string;
}

export interface Converted {
  readonly program: Program;
  readonly notConverted: readonly NotConverted[];
}

type SpecFunction = (args: never) => unknown;

/** The conditions of one definition that a callback evaluates, with the arguments and their schemas. */
interface Slot {
  readonly callback: keyof Program;
  readonly definition: DefinitionRef;
  readonly conditions: Conditions<never> | undefined;
  readonly args: readonly Arg[];
  readonly shapes: readonly (Shape | undefined)[];
  /** Whether the callback takes the conditions only all together, as `firstFailing` runs them. */
  readonly whole: boolean;
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

function slotsOf(spec: Spec): Slot[] {
  const slots: Slot[] = [];
  for (const { service, name, definition: d } of spec.definitions) {
    const definition = { service, name };
    if (d.kind === "command" || d.kind === "query") {
      const target = d as AnyCommand | AnyQuery;
      const payloads = target.kind === "command" ? target.emits.map((e) => e.payload) : [];
      slots.push(
        {
          callback: "requires",
          definition,
          conditions: target.requires,
          args: ["input"],
          shapes: [target.input],
          whole: false,
        },
        {
          callback: "ensures",
          definition,
          conditions: target.ensures,
          args: ["input", "output", "events"],
          shapes: [target.input, target.output, ...payloads],
          whole: false,
        },
      );
    }
    if (d.kind === "screen") {
      const screen = d as ChartSpec;
      slots.push(
        {
          callback: "requires",
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
  for (const [service, { definition }] of spec.services)
    for (const [name, entity] of Object.entries(definition.entities as Readonly<Record<string, AnyEntity>>))
      slots.push({
        callback: "invariants",
        definition: { service, name },
        conditions: entity.invariants as Conditions<never>,
        args: ["record"],
        shapes: [entity.fields],
        whole: true,
      });
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
    const lists: Record<keyof Program, Condition[]> = { requires: [], ensures: [], invariants: [], closeEnsures: [] };
    const notConverted: NotConverted[] = [];
    for (const slot of slotsOf(spec)) {
      const entries = Object.entries(slot.conditions ?? {}) as [string, SpecFunction][];
      const codec = slot.shapes.some((shape) => shape !== undefined && holdsCodec(shape));
      const conditions: Condition[] = [];
      const failed: NotConverted[] = [];
      for (const [name, f] of entries) {
        const at = { callback: slot.callback, definition: slot.definition, name };
        const body = codec ? { unconverted: "receives a value of a codec" } : this.convert(f, slot.args);
        if ("unconverted" in body) failed.push({ ...at, reason: body.unconverted });
        else conditions.push({ definition: slot.definition, name, body });
      }
      notConverted.push(...failed);
      if (!slot.whole || failed.length === 0) lists[slot.callback].push(...conditions);
    }
    return { program: lists, notConverted };
  }
}
