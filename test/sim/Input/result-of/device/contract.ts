import { contract } from "@natsuzora-dev/tazuna";
import { granted, requestPermission } from "./device.ts";

export const device = contract({ granted, requestPermission });
