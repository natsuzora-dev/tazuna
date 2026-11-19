import { contract, denied, granted, requestPermission } from "./device.ts";

export const device = contract({ granted, denied, requestPermission });
