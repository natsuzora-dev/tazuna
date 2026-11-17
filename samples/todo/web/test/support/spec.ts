import { join } from "node:path";
import { checkSpec, failureText } from "@natsuzora-dev/tazuna/verify";

const checked = await checkSpec(join(import.meta.dirname, "../../../spec"));
if (checked.kind !== "checked") throw new Error(failureText(checked, "spec"));
export const spec = checked.spec;
