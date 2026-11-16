import { contract } from "@natsuzora-dev/tazuna";
import { ask, status } from "./app.ts";

export const app = contract({ ask, status });
