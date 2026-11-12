import { contract } from "@natsuzora-dev/tazuna";
import { noticed } from "./events.ts";

export const notifier = contract({ noticed });
