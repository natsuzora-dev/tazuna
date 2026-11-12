import { contract } from "@natsuzora-dev/tazuna";
import { playSound, showNotification } from "./device.ts";

export const device = contract({ showNotification, playSound });
