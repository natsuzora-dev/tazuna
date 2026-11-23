import { emit } from "@natsuzora-dev/tazuna";
import { command } from "./data.ts";
import { added, built, checked, failed, noted, pinged } from "./events.ts";

export const run = command({ callers: ["client", "todo"], emits: [failed] }).decide(() => [emit(failed, {})]);
export const build = command({ callers: ["client", "todo"], emits: [built] }).decide(() => [emit(built, {})]);
export const checkBuild = command({ callers: ["client", "todo"], emits: [checked] }).decide(() => [emit(checked, {})]);
export const ping = command({ callers: ["client", "todo"], emits: [pinged] }).decide(() => [emit(pinged, {})]);
export const noteFromA = command({ callers: ["client", "todo"], emits: [noted] }).decide(() => [emit(noted, {})]);
export const noteFromB = command({ callers: ["client", "todo"], emits: [noted] }).decide(() => [emit(noted, {})]);
export const add = command({ callers: ["client", "todo"], emits: [added] }).decide(() => [emit(added, {})]);
