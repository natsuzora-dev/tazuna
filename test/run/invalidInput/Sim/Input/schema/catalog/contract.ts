import { contract } from "@natsuzora-dev/tazuna";
import { Item, numbers } from "./catalog.ts";

export const catalog = contract({ Item, numbers });
