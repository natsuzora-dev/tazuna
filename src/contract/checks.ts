import type { Conditions } from "../dsl/conditions.ts";
import type { AnyCommand, AnyQuery, Emit } from "../dsl/definition.ts";

const readsRecords = Symbol("reads records");
const unreadableRecords = new Proxy(
  {},
  {
    get: () => {
      throw readsRecords;
    },
  },
);

function firstFailingIgnoringRecords(conditions: Conditions<unknown>, args: object): string | undefined {
  for (const [name, condition] of Object.entries(conditions)) {
    try {
      if (!condition({ ...args, records: unreadableRecords })) return name;
    } catch (error) {
      if (error !== readsRecords) throw error;
    }
  }
  return undefined;
}

/**
 * Returns the first ensures of the target that fails without reading records, skipping each ensures that reads them.
 */
export const assumedEnsures = (
  target: AnyCommand | AnyQuery,
  args: { readonly input: unknown; readonly output?: unknown; readonly events?: readonly Emit[] },
): string | undefined => firstFailingIgnoringRecords(target.ensures as Conditions<unknown>, args);
