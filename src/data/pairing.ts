import { existsSync, readdirSync } from "node:fs";
import type { DefinitionRef } from "./definitionRef.ts";
import type { Run } from "./traceFile.ts";
import type { Uncomparable } from "./uncomparable.generated.ts";

export interface Entry {
  readonly name: string;
  readonly kind: "file" | "folder" | "other";
}

/** Returns the entries of the folder sorted by name, or none when the folder does not exist. */
export function entriesOf(folder: string): Entry[] {
  if (!existsSync(folder)) return [];
  return readdirSync(folder, { withFileTypes: true })
    .map((e): Entry => ({ name: e.name, kind: e.isFile() ? "file" : e.isDirectory() ? "folder" : "other" }))
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/** The subfolder `service` of the trace folder, or the snapshot folder of `service`. */
export interface Folder {
  readonly service: string;
  readonly entries: readonly Entry[];
}

export type TraceEntry = { readonly kind: "traceEntry"; readonly service?: string; readonly entry: string };
export type SnapshotEntry = { readonly kind: "snapshotEntry"; readonly service: string; readonly entry: string };
export type ScenarioAt = { readonly kind: "scenario"; readonly scenario: DefinitionRef };

/** An entry of the trace folder or of its subfolder `service`, an entry of the snapshot folder of `service`, or a scenario. */
export type At = TraceEntry | SnapshotEntry | ScenarioAt;

export interface PairingViolation<A extends At = At> {
  readonly at: A;
  readonly violation: Uncomparable;
}

export interface Expected {
  readonly run: Run;
  /**
   * Whether the run is compared. A compared run's file is compared when present and reported when missing; the file of
   * a run that is not compared is ignored.
   */
  readonly compared: boolean;
}
