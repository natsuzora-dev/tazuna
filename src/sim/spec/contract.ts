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
export function ensured(condition: (args: never) => boolean, args: object): "holds" | "fails" | "readsRecords" {
  try {
    return condition({ ...args, records: unreadableRecords } as never) ? "holds" : "fails";
  } catch (error) {
    if (error === readsRecords) return "readsRecords";
    throw error;
  }
}
