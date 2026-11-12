import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { logTitle } from "./todo.ts";

export const logEmpty = scenario(
  "Log an empty title; the refinement of the payload schema of titleLogged throws, so test reports exception of titleLogged",
  [at("2026-10-25T09:00:00+09:00"), send(logTitle, { title: "" })],
);
