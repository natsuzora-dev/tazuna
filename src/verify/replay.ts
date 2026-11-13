import type { TraceLine } from "../data/trace.generated.ts";
import { type Bindings, contentOf, nameOf, renamed } from "../data/trace.ts";
import { canonicalJson, type Json } from "../data/values.ts";

/**
 * Maps each key that `snapshotRequest` created to the string that the implementation's `request` has in its place, when
 * `request` equals `snapshotRequest` renamed by `renaming` except for those keys. Returns `undefined` otherwise, and
 * when two created keys map to one string.
 */
export function matchRequest(snapshotRequest: TraceLine, request: TraceLine, renaming: Bindings): Bindings | undefined {
  if (snapshotRequest.type !== request.type || nameOf(snapshotRequest) !== nameOf(request)) return undefined;
  const created = "created" in snapshotRequest ? (snapshotRequest.created ?? []) : [];
  const keys = new Map<string, string>();
  const matches = (snapshot: unknown, implementation: unknown): boolean => {
    if (typeof snapshot === "string" && created.includes(snapshot)) {
      if (typeof implementation !== "string" || (keys.get(snapshot) ?? implementation) !== implementation) return false;
      keys.set(snapshot, implementation);
      return true;
    }
    if (typeof snapshot === "string") return (renaming.get(snapshot) ?? snapshot) === implementation;
    if (Array.isArray(snapshot))
      return (
        Array.isArray(implementation) &&
        snapshot.length === implementation.length &&
        snapshot.every((s, i) => matches(s, implementation[i]))
      );
    if (snapshot !== null && typeof snapshot === "object") {
      if (implementation === null || typeof implementation !== "object" || Array.isArray(implementation)) return false;
      const s = snapshot as Record<string, unknown>;
      const t = implementation as Record<string, unknown>;
      return [...new Set([...Object.keys(s), ...Object.keys(t)])].every((k) => matches(s[k], t[k]));
    }
    return canonicalJson(snapshot) === canonicalJson(implementation);
  };
  const matched = matches(contentOf(snapshotRequest), contentOf(request));
  return matched && new Set(keys.values()).size === keys.size ? keys : undefined;
}

/** Returns `line` with each string that `renaming` maps replaced by the string that it maps to. */
export const rename = <L extends TraceLine>(line: L, renaming: Bindings): L => renamed(renaming, line as Json) as L;
