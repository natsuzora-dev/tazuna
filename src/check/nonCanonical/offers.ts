import type { Expression } from "oxc-parser";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { AnyControl } from "../../dsl/definition.ts";
import type { Found } from "../../load/found.ts";
import { placeIn, type Spec } from "../../load/load.ts";
import { propertiesOf, property, unwrap, writtenOf } from "./ast.ts";

/** The elements of the array literal that the function `node` returns whatever it reads, if it returns only one. */
function constantArray(node: Expression) {
  const fn = unwrap(node);
  if ((fn.type !== "ArrowFunctionExpression" && fn.type !== "FunctionExpression") || fn.async || fn.generator)
    return undefined;
  const body = fn.body;
  if (body === null) return undefined;
  const [only, ...rest] = body.type === "BlockStatement" ? body.body : [];
  const returned =
    body.type !== "BlockStatement"
      ? body
      : only?.type === "ReturnStatement" && rest.length === 0
        ? (only.argument ?? undefined)
        : undefined;
  const array = returned === undefined ? undefined : unwrap(returned);
  return array?.type === "ArrayExpression" ? array.elements : undefined;
}

/** The marker that writes the offers entry `offer` of a control with the payload `payload`, if one does. */
function markerOf(offer: Expression, payload: object): "none" | "any" | undefined {
  const elements = constantArray(offer);
  if (elements === undefined) return undefined;
  if (elements.length === 0) return "none";
  const [only] = elements;
  const fieldless = Object.keys(payload).length === 0;
  return fieldless && elements.length === 1 && only?.type === "ObjectExpression" && only.properties.length === 0
    ? "any"
    : undefined;
}

export const check = (spec: Spec): Found<NonCanonical>[] =>
  writtenOf(spec).flatMap(({ source, definition, calls }) => {
    if (definition?.definition.kind !== "screen") return [];
    const controls = definition.definition.controls as Readonly<Record<string, AnyControl>>;
    const chart = calls.find((c) => c.method === "chart")?.arguments[0];
    if (chart === undefined || chart.type === "SpreadElement") return [];
    const states = property(chart, "states");
    const offers: [string | null, Expression | undefined][] = [
      [null, property(chart, "offers")],
      ...(states === undefined ? [] : propertiesOf(states)).map(([state, p]): [string, Expression | undefined] => [
        state,
        property(p.value, "offers"),
      ]),
    ];
    return offers.flatMap(([state, written]) =>
      written === undefined
        ? []
        : propertiesOf(written).flatMap(([control, p]): Found<NonCanonical>[] => {
            const marker = markerOf(p.value, controls[control]?.payload ?? {});
            if (marker === undefined) return [];
            const ref = { service: definition.service, name: definition.name };
            return [
              {
                violation: { kind: "NonCanonical.constantOffer", definition: ref, data: { state, control, marker } },
                place: placeIn(source, p.start),
              },
            ];
          }),
    );
  });
