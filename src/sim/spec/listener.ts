import { reversedBags } from "../../data/bag.ts";
import type { StepName } from "../../data/step.generated.ts";
import type { Obligation } from "../../data/uncovered.ts";
import { type Collect, InstrumentedFunctions, type InstrumentFunctions } from "../../explore/instrument.ts";
import type { Spec } from "../../load/load.ts";
import { sorting } from "../../service/functions.ts";
import type { InstanceId } from "../../service/instance.ts";
import { type Note, type RecordPart, type RegionCheck, type ValueKey, valueName } from "../../service/note.ts";
import type { Evaluations } from "../../service/state.ts";

import { Cache } from "./cache.ts";
import { Coverage } from "./coverage.ts";
import { SpecFunctions } from "./functions.ts";

/** The evaluation cache's name for the time, which no valueName can be. */
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
  private read(key: ValueKey): void {
    const name = valueName(key);
    this.cache.read(name);
    this.collected.read(name);
  }

  private write(key: ValueKey, keyWrite: boolean): void {
    this.cache.wrote(valueName(key));
    this.collected.write(key, keyWrite);
  }

  stepBegins(step: number, name: StepName, started: InstanceId | undefined): void {
    this.collected.stepBegins(step, name, started);
  }
  arrivalBegins(step: number, name: StepName): void {
    this.collected.arrivalBegins(step, name);
  }
  arrivalEnds(): void {
    this.collected.arrivalEnds();
  }
  stepEnds(): void {
    this.collected.stepEnds();
  }
  settlesAround(owner: InstanceId): void {
    this.collected.settlesAround(owner);
  }
  readStates(states: readonly (readonly [InstanceId, string])[]): void {
    if (!this.cache.quiet) for (const [id, state] of states) this.read({ kind: "state", id, state });
  }
  wroteState(id: InstanceId, state: string): void {
    this.write({ kind: "state", id, state }, false);
  }
  wroteCopies(id: InstanceId, map: string): void {
    this.write({ kind: "state", id, state: map }, false);
  }
  wroteShown(id: InstanceId, slot: string): void {
    this.write({ kind: "shown", id, slot }, false);
  }
  transitionPart(part: number): void {
    this.collected.transitionPart(part);
  }
  microstepEnds(check: RegionCheck): void {
    this.collected.microstepEnds(check);
  }
  afterMessageBegins(message: number): void {
    this.collected.afterMessageBegins(message);
  }
  afterMessageEnds(): void {
    this.collected.afterMessageEnds();
  }
  readRecord(part: RecordPart): void {
    if (!this.cache.quiet) this.read({ kind: "record", part });
  }
  wroteRecord(part: RecordPart, keyWrite: boolean): void {
    this.write({ kind: "record", part }, keyWrite);
  }
  readContext(id: InstanceId, field: string): void {
    if (!this.cache.quiet) this.read({ kind: "context", id, field });
  }
  wroteContext(id: InstanceId, field: string): void {
    this.write({ kind: "context", id, field }, false);
  }
  readShown(id: InstanceId, slot: string): void {
    if (!this.cache.quiet) this.read({ kind: "shown", id, slot });
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

  replayIfFresh(id: InstanceId, part: string): boolean {
    const reads = this.cache.freshReads(id, part);
    if (reads === undefined) return false;
    if (!this.cache.quiet)
      for (const name of reads) {
        this.cache.read(name);
        if (name !== now) this.collected.read(name);
      }
    return true;
  }
  track(f: () => void): string[] {
    return this.cache.track(f);
  }
  remember(id: InstanceId, part: string, reads: readonly string[], watched: readonly string[]): void {
    this.cache.remember(id, part, reads, watched);
  }
  quietly<T>(f: () => T): T {
    return this.cache.quietly(f);
  }
}

/**
 * Returns Lean's `instrument st (fs.sorting st) ifs` over the spec's functions. A question asked again with Bags in reverse order
 * reads quietly, so neither the open step nor the evaluation cache hears its reads.
 */
export function instrumented(spec: Spec, service: string, listener: Listener): InstrumentedFunctions {
  const own = new SpecFunctions(spec, service);
  const functions = sorting(own.st, own);
  const reversed: InstrumentFunctions["reversed"] = (call) =>
    listener.quietly(() => reversedBags(() => call(functions)));
  return new InstrumentedFunctions(own.st, functions, { reversed }, listener.collected);
}
