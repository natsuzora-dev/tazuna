import { join } from "node:path";
import { loadSpec } from "@natsuzora-dev/tazuna/load";

export const spec = await loadSpec(join(import.meta.dirname, "../../../spec"));
