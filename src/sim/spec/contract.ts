import type { Ensured } from "../../data/ensured.generated.ts";
import type { Conditions } from "../../dsl/conditions.ts";
import { firstFalse, passes } from "../../service/functions.ts";

const readsRecords = Symbol("reads records");
const unreadableRecords = new Proxy(
  {},
  {
    get: () => {
      throw readsRecords;
    },
  },
);

/**
 * Returns what the ensures `condition` gives on a request's results `args`: whether it holds, or that it reads records,
 * which are the target's own and not the caller's.
 */
export function ensured(condition: (args: never) => boolean, args: object): Ensured {
  try {
    return condition({ ...args, records: unreadableRecords } as never) ? "holds" : "fails";
  } catch (error) {
    if (error === readsRecords) return "readsRecords";
    throw error;
  }
}

/** The first of `ensures` that fails on a request's results `args`, skipping those that pass (Ensured.passes). */
export const firstFailedEnsures = (ensures: Conditions<never>, args: object): string | undefined =>
  firstFalse(([, condition]) => passes(ensured(condition, args)), Object.entries(ensures))?.[0];
