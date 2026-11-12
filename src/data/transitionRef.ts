/** A reference to a transition. `state` is null for the chart's own `on`. */
export type TransitionRef = {
  readonly state: string | null;
  readonly keys: readonly string[];
  readonly index: number;
};
