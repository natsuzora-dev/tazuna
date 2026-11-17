import { reversedBags } from "../../data/bag.ts";
import type { StepName } from "../../data/choiceDependent.generated.ts";
import type { Obligation } from "../../data/uncovered.ts";
import {
  type Collect,
  contextKey,
  InstrumentedFunctions,
  type InstrumentFunctions,
  shownKey,
} from "../../explore/instrument.ts";
import type { Spec } from "../../load/load.ts";
import { type Note, type RecordPart, type RegionCheck, recordPartName, stateValueName } from "../../service/note.ts";
import type { Evaluations } from "../../service/state.ts";
import { Cache } from "./cache.ts";
import { Coverage } from "./coverage.ts";
import { SpecFunctions } from "./functions.ts";

/** The evaluation cache's name for the time, which no value's key can be. */
const now = "@now";

/**
 * The note that a TS run listens with: Lean's Collect, the evaluation cache (which the reads and writes keep current),
 * and the coverage hits, request pairs and unchosen tie that explore reads. It turns each note into the values that
 * both Collect and the evaluation cache hear.
 */
export class Listener implements Note, Evaluations {
  readonly spec: Spec;
  readonly collected: Collect;
  private readonly cache: Cache;
  readonly coverage: Coverage;

  constructor(spec: Spec, collected: Collect, cache = new Cache(), coverage = new Coverage()) {
    this.spec = spec;
    this.collected = collected;
    this.cache = cache;
    this.coverage = coverage;
  }

  /** Records a read of `key`. Inside `quietly` no read counts, so the callers skip building the key. */
  private read(key: string): void {
    this.cache.read(key);
    this.collected.read(key);
  }

  private write(key: string, keyWrite: boolean): void {
    this.cache.wrote(key);
    this.collected.write(key, keyWrite);
  }

  events(step: number, start: number, groups: readonly number[]): void {
    this.collected.events(step, start, groups);
  }
  stepBegins(step: number, name: StepName, startedResource: string | undefined): void {
    this.collected.stepBegins(step, name, startedResource);
  }
  stepEnds(): void {
    this.collected.stepEnds();
  }
  settlesAround(owner: string): void {
    this.collected.settlesAround(owner);
  }
  readStates(states: readonly (readonly [string, string])[]): void {
    if (!this.cache.quiet) for (const [resource, state] of states) this.read(stateValueName(resource, state));
  }
  wroteState(resource: string, state: string): void {
    this.write(stateValueName(resource, state), false);
  }
  wroteCopies(resource: string, map: string): void {
    this.write(stateValueName(resource, map), false);
  }
  wroteShown(resource: string, slot: string): void {
    this.write(shownKey(resource, slot), false);
  }
  transitionPart(part: number): void {
    this.collected.transitionPart(part);
  }
  microstepEnds(check: RegionCheck): void {
    this.collected.microstepEnds(check);
  }
  readRecord(part: RecordPart): void {
    if (!this.cache.quiet) this.read(recordPartName(part));
  }
  wroteRecord(part: RecordPart, keyWrite: boolean): void {
    this.write(recordPartName(part), keyWrite);
  }
  readContext(resource: string, field: string): void {
    if (!this.cache.quiet) this.read(contextKey(resource, field));
  }
  wroteContext(resource: string, field: string): void {
    this.write(contextKey(resource, field), false);
  }
  readShown(resource: string, slot: string): void {
    if (!this.cache.quiet) this.read(shownKey(resource, slot));
  }
  readNow(): void {
    if (!this.cache.quiet) this.cache.read(now);
  }
  wroteNow(): void {
    this.cache.wrote(now);
  }

  reached(obligation: Obligation): void {
    this.coverage.reach(obligation);
  }

  replayIfFresh(resource: string, part: string): boolean {
    const reads = this.cache.freshReads(resource, part);
    if (reads === undefined) return false;
    if (!this.cache.quiet)
      for (const key of reads) {
        if (key === now) this.readNow();
        else this.read(key);
      }
    return true;
  }
  track(f: () => void): string[] {
    return this.cache.track(f);
  }
  remember(resource: string, part: string, reads: readonly string[], watched: readonly string[]): void {
    this.cache.remember(resource, part, reads, watched);
  }
  quietly<T>(f: () => T): T {
    return this.cache.quietly(f);
  }
}

/**
 * Returns Lean's `instrument st fs ifs` over the spec's functions. A question asked again with Bags in reverse order
 * reads quietly, so neither the open step nor the evaluation cache hears its reads, and it asks functions without the
 * listener, so that it reaches no coverage.
 */
export function instrumented(spec: Spec, service: string, listener: Listener): InstrumentedFunctions {
  const functions = new SpecFunctions(spec, service, listener);
  const unheard = new SpecFunctions(spec, service);
  const reversed: InstrumentFunctions["reversed"] = (call) => listener.quietly(() => reversedBags(() => call(unheard)));
  return new InstrumentedFunctions(functions.st, functions, { reversed }, listener.collected);
}
