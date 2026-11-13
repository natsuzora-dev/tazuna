import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { Fields, Json } from "../../data/values.ts";
import { isDescendant } from "../../syntax/tree.ts";
import { reaches } from "../chart/select.ts";
import { Failed, issueViolation } from "../functions.ts";
import { ref } from "../service/basic.ts";
import { LazyRecordSource } from "../service/records.ts";
import {
  copyName,
  documentOrder,
  halt,
  type Instance,
  machine,
  NoteAccess,
  type Run,
  type State,
  scopeOf,
} from "../state.ts";

/**
 * An operation that a screen accepts. When `payloads` is undefined, it accepts every payload that matches the schema.
 */
export interface Operation {
  readonly screen: string;
  readonly control: string;
  readonly payloads: readonly unknown[] | undefined;
}

/** Returns the open screen instance that takes an operation on `screen`, or the reason that none does. */
function topOf(
  s: State,
  screen: string,
):
  | { readonly kind: "notOpen" }
  | { readonly kind: "covered"; readonly child: Instance }
  | { readonly kind: "ok"; readonly instance: Instance } {
  for (const resource of s.stack.toReversed()) {
    const instance = machine(s, resource);
    if (instance === undefined) continue;
    if (instance.chart.name === screen) return { kind: "ok", instance };
    const opener = instance.opener;
    if (opener === undefined) continue;
    if (opener.modal) return { kind: "covered", child: instance };
  }
  return { kind: "notOpen" };
}

/**
 * Returns the checked payloads that the offers of the screen list, per offering state (null for the chart's own
 * offers).
 */
function offered(
  r: Run,
  screen: string,
  top: Instance,
  key: string,
  payload: unknown,
): {
  readonly state: string | null;
  readonly payloads: readonly { readonly value: Fields; readonly encoded: unknown }[];
}[] {
  const chart = top.chart;
  const found = documentOrder(r.state, top).flatMap(({ holder, n }) => {
    if (!holder.entered.has(n) || (holder !== top && !reaches(r, holder, payload))) return [];
    return chart.states.get(n)?.offers.includes(key) === true ? [{ holder, state: n }] : [];
  });
  const innermost = found.filter(
    (a) => !found.some((b) => b.state !== a.state && isDescendant(chart.tree, b.state, a.state)),
  );
  const applied: { readonly holder: Instance; readonly state: string | null }[] =
    innermost.length > 0 || !chart.offers.includes(key) ? innermost : [{ holder: top, state: null }];
  const definition = ref(r.st, screen);
  return applied.map(({ holder, state }) => {
    const scope = scopeOf(r.state, holder, state);
    const payloads = r.functions.offers(
      scope,
      new LazyRecordSource(r.state.records, r.note),
      key,
      new NoteAccess(r, scope),
    );
    if (!(payloads instanceof Failed)) return { state, payloads };
    return halt(
      issueViolation(definition, payloads, () => ({
        kind: "Fault.offersSchema",
        definition,
        data: { control: key, state },
      })),
    );
  });
}

/**
 * Returns the instance that takes the operation with `payload` now, or the reason that the screen does not accept it.
 */
export function accepting(
  r: Run,
  screen: string,
  key: string,
  payload: { readonly value: Fields; readonly encoded: unknown },
):
  | { readonly top: Instance }
  | { readonly child: DefinitionRef }
  | { readonly payload: Json }
  | { readonly closed: true } {
  const found = topOf(r.state, screen);
  if (found.kind === "notOpen") return { closed: true };
  if (found.kind === "covered") return { child: ref(r.st, found.child.chart.name) };
  const top = { top: found.instance };
  const applied = offered(r, screen, found.instance, key, payload.value);
  if (applied.length === 0) return top;
  const asked = JSON.stringify(payload.encoded);
  const lists = applied.some(({ payloads }) => payloads.some((o) => JSON.stringify(o.encoded) === asked));
  return lists ? top : { payload: payload.encoded as Json };
}

/**
 * Returns the operations that `screen` accepts now. Offers are evaluated for the payload sent to all copies (without
 * key fields) and for each copy's key payload, since the key decides which copy receives it. If any of them has no
 * applicable offers, every payload that matches the schema is accepted (`[{}]` without payload fields); otherwise, only
 * the offered payloads that are accepted are listed.
 */
export function operationsOf(r: Run, screen: string): Operation[] {
  const found = topOf(r.state, screen);
  if (found.kind !== "ok") return [];
  const top = found.instance;
  const copies = [...top.copyKeys].flatMap(([map, keys]) =>
    top.entered.has(map)
      ? keys.flatMap((k) => {
          const copy = machine(r.state, copyName(top.resource, map, k))?.copyOf;
          return copy === undefined ? [] : [copy.key as Fields];
        })
      : [],
  );
  return top.chart.controls.flatMap(({ name: key, hasPayload }): Operation[] => {
    const applied = [{}, ...copies].map((reach) => offered(r, screen, top, key, reach));
    if (applied.some((offered) => offered.length === 0))
      return [{ screen, control: key, payloads: hasPayload ? undefined : [{}] }];
    const listed = new Map<string, { readonly value: Fields; readonly encoded: unknown }>();
    for (const { payloads } of applied.flat()) for (const o of payloads) listed.set(JSON.stringify(o.encoded), o);
    const payloads = [...listed.values()]
      .filter((o) => copies.length === 0 || "top" in accepting(r, screen, key, o))
      .map((o) => o.encoded);
    return payloads.length === 0 ? [] : [{ screen, control: key, payloads }];
  });
}
