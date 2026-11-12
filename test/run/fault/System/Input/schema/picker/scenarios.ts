import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { filteredScreen, listScreen } from "./picker.ts";

export const pickListed = scenario("Pick a task from the list; test reports rootOffersSchema", [
  at("2026-10-25T09:00:00+09:00"),
  operate(listScreen, "pick", { taskId: "task-1" }),
]);

export const pickFiltered = scenario("Pick a task from the filtered list; test reports offersSchema", [
  at("2026-10-25T09:00:00+09:00"),
  operate(filteredScreen, "pick", { taskId: "task-1" }),
]);
