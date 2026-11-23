import { join } from "node:path";
import { checkSpecUnconverted, failureText } from "@natsuzora-dev/tazuna/verify";

const checked = await checkSpecUnconverted(join(import.meta.dirname, "../../../spec"));
if (checked.kind !== "checked") throw new Error(failureText(checked, "spec"));
export const spec = checked.spec;
