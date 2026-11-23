import { now } from "./now.ts";

export const wallClock = (): string => now().toISOString();
