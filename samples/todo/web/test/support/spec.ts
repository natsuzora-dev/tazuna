import { join } from "node:path";
import { checkSpec } from "@natsuzora-dev/tazuna/verify";

const checked = await checkSpec(join(import.meta.dirname, "../../../spec"));
if (checked.kind !== "checked") throw new Error(`the spec does not pass tazuna check: ${JSON.stringify(checked)}`);
export const spec = checked.spec;
