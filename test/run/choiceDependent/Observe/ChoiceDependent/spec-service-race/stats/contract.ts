import { contract, countCompleted, resetCount, resumeCounting } from "./stats.ts";

export const stats = contract({ countCompleted, resetCount, resumeCounting });
