import type { Expression } from "oxc-parser";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { type LoadedSpec, placeIn } from "../../load/load.ts";
import { propertiesOf, unwrap, writtenOf } from "./ast.ts";

type Path = readonly (string | number)[];

/**
 * Whether `{}` at `path` means something that leaving it out does not: in the definer's options, a state of the states'
 * tree, which has no keywords, or a map state's `key`, which has no fields; in `chart()`, a shows slot without input.
 */
const meaningful = (path: Path, definer: boolean): boolean =>
  definer ? path.at(-2) === "states" || path.at(-1) === "key" : path.at(-2) === "shows";

/** Each keyword within `node`, at `path`, written as `{}`. */
function empties(node: Expression, path: Path, definer: boolean): { path: Path; node: Expression }[] {
  const e = unwrap(node);
  if (e.type === "ArrayExpression")
    return e.elements.flatMap((element, i) =>
      element === null || element.type === "SpreadElement" ? [] : empties(element, [...path, i], definer),
    );
  if (e.type !== "ObjectExpression") return [];
  if (e.properties.length === 0)
    return typeof path.at(-1) === "string" && !meaningful(path, definer) ? [{ path, node: e }] : [];
  return propertiesOf(e).flatMap(([key, p]) => empties(p.value, [...path, key], definer));
}

export const check = (spec: LoadedSpec): Found<NonCanonical>[] =>
  writtenOf(spec).flatMap(({ source, definition, service, calls }) =>
    calls.flatMap(({ method, arguments: args }) =>
      args.flatMap((arg) =>
        arg.type === "SpreadElement"
          ? []
          : empties(arg, [], method === null).map(
              ({ path, node }): Found<NonCanonical> => ({
                violation:
                  definition === null
                    ? { kind: "NonCanonical.emptyKeyword", definition: null, data: { service, path } }
                    : {
                        kind: "NonCanonical.emptyKeyword",
                        definition: { service, name: definition.name },
                        data: { path },
                      },
                place: placeIn(source, node.start),
              }),
            ),
      ),
    ),
  );
