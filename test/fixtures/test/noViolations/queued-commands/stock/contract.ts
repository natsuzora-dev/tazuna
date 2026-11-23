import { contract, count, prepare, start } from "./stock.ts";

export const stock = contract({ start, prepare, count });
