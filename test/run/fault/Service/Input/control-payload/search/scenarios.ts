import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { searchScreen } from "./search.ts";

export const searchEmpty = scenario(
  "Search with an empty query; the refinement of the payload schema of search throws, so test reports exception of searchScreen",
  [at("2026-10-25T09:00:00+09:00"), operate(searchScreen, "search", { query: "" })],
);
