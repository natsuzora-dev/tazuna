import { at, scenario, service } from "@natsuzora-dev/tazuna";

export const { event } = service({ description: "Keep the tasks" });

export const taskAdded = event({});

export const startsDay = scenario("Start in the morning", [at("2026-10-25T09:00:00+09:00")]);
