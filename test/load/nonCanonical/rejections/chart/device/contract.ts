import { beep, contract, notify } from "./device.ts";

export const device = contract({ notify, beep });
