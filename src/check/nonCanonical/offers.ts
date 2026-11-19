import { parseSync } from "oxc-parser";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { AnyControl } from "../../dsl/definition.ts";
import { writtenOptions } from "../../dsl/written.ts";
import type { Found } from "../../load/found.ts";
import type { Spec } from "../../load/load.ts";

interface Node {
  readonly type?: string;
  readonly body?: Node | readonly Node[];
  readonly expression?: Node;
  readonly argument?: Node | null;
  readonly elements?: readonly (Node | null)[];
  readonly properties?: readonly Node[];
}

type Written = Readonly<Record<string, unknown>>;

/** The elements of the array literal that the function `f` returns whatever it reads, if it returns only one. */
function constantArray(f: unknown): readonly (Node | null)[] | undefined {
  if (typeof f !== "function") return undefined;
  const { program, errors } = parseSync("offer.js", `(${f.toString()})`);
  if (errors.length > 0) return undefined;
  let fn = (program.body[0] as Node | undefined)?.expression;
  while (fn?.type === "ParenthesizedExpression") fn = fn.expression;
  const body = fn?.body;
  if (body === undefined || Array.isArray(body)) return undefined;
  const statements = (body as Node).type === "BlockStatement" ? ((body as Node).body as readonly Node[]) : undefined;
  const returned = statements === undefined ? (body as Node) : statements.length === 1 ? statements[0]?.argument : null;
  return returned?.type === "ArrayExpression" ? returned.elements : undefined;
}

/** The marker that writes the offers entry `offer` of a control with the payload `payload`, if one does. */
function markerOf(offer: unknown, payload: object): "none" | "any" | undefined {
  const elements = constantArray(offer);
  if (elements === undefined) return undefined;
  if (elements.length === 0) return "none";
  const [only] = elements;
  const fieldless = Object.keys(payload).length === 0;
  return fieldless && elements.length === 1 && only?.type === "ObjectExpression" && only.properties?.length === 0
    ? "any"
    : undefined;
}

const entries = (object: unknown): [string, Written][] =>
  typeof object === "object" && object !== null ? (Object.entries(object) as [string, Written][]) : [];

export const check = (spec: Spec): Found<NonCanonical>[] =>
  spec.definitions.flatMap((d) => {
    if (d.definition.kind !== "screen") return [];
    const controls = d.definition.controls as Readonly<Record<string, AnyControl>>;
    const [, chart] = writtenOptions(d.definition) as readonly Written[];
    const offers: [string | null, Written][] = [
      [null, (chart?.["offers"] ?? {}) as Written],
      ...entries(chart?.["states"]).map(([state, row]): [string, Written] => [state, (row["offers"] ?? {}) as Written]),
    ];
    return offers.flatMap(([state, written]) =>
      Object.entries(written).flatMap(([control, offer]): Found<NonCanonical>[] => {
        const marker = markerOf(offer, controls[control]?.payload ?? {});
        if (marker === undefined) return [];
        const definition = { service: d.service, name: d.name };
        return [
          {
            violation: { kind: "NonCanonical.constantOffer", definition, data: { state, control, marker } },
            place: d.place,
          },
        ];
      }),
    );
  });
