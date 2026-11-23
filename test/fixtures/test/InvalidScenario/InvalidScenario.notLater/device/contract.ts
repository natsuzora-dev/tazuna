import { contract, granted, muted, requestPermission } from "./device.ts";

export const device = contract({ requestPermission, granted, muted });
