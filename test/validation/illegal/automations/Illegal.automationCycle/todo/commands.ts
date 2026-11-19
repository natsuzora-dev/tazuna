import { emit } from "@natsuzora-dev/tazuna";
import { command } from "./data.ts";
import { added, built, checked, failed, noted, pinged } from "./events.ts";

export const run = command({ emits: [failed] }).decide(() => [emit(failed, {})]);
export const build = command({ emits: [built] }).decide(() => [emit(built, {})]);
export const checkBuild = command({
  emits: [checked],
}).decide(() => [emit(checked, {})]);
export const ping = command({ emits: [pinged] }).decide(() => [emit(pinged, {})]);
export const noteFromA = command({ emits: [noted] }).decide(() => [emit(noted, {})]);
export const noteFromB = command({ emits: [noted] }).decide(() => [emit(noted, {})]);
export const add = command({ emits: [added] }).decide(() => [emit(added, {})]);
