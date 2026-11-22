import { traceNameOfRef } from "../spec/structure.ts";
import type { Spec } from "./load.ts";

/** Returns traceNameOfRef of the definition `d`, or `?` when `d` is not a named definition. */
export function traceName(spec: Spec, d: unknown, from?: string): string {
  const named = spec.names.get(d);
  return named === undefined ? "?" : traceNameOfRef(named, from);
}
