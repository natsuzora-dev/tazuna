/** Milliseconds since the Unix epoch. Services read time only through a clock, so tests can move it. */
export interface Clock {
  now(): number;
}

export const systemClock: Clock = { now: () => Date.now() };

/** A clock that moves only when told to. */
export class ManualClock implements Clock {
  #now: number;

  constructor(start: number) {
    this.#now = start;
  }

  now(): number {
    return this.#now;
  }

  set(time: number): void {
    this.#now = time;
  }

  advance(ms: number): void {
    this.#now += ms;
  }
}
