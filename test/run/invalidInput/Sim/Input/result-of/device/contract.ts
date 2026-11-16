import { contract } from "@natsuzora-dev/tazuna";
import { denied, granted, requestPermission } from "./device.ts";

export const device = contract({ granted, denied, requestPermission });
