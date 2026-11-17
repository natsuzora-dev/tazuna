/** What fires a transition array: the key that the chart writes the array under, typed per keyword. */
export type Trigger =
  | { readonly type: "on"; readonly key: string }
  | { readonly type: "after"; readonly deadline: string }
  | { readonly type: "always" }
  | { readonly type: "onDone" }
  | { readonly type: "calls"; readonly key: string; readonly outcome: "onFulfilled" | "onRejected" }
  | { readonly type: "sends"; readonly key: string; readonly outcome: "onAccepted" | "onRejected" }
  /** The `onDone` of an `opens`, taken when the opened screen closes. */
  | { readonly type: "opens"; readonly key: string };

/** A reference to a transition. `state` is null for the chart's own `on`. */
export type TransitionRef = {
  readonly state: string | null;
  readonly trigger: Trigger;
  readonly index: number;
};

export function sameTrigger(a: Trigger, b: Trigger): boolean {
  switch (a.type) {
    case "always":
    case "onDone":
      return b.type === a.type;
    case "after":
      return b.type === "after" && b.deadline === a.deadline;
    case "on":
    case "opens":
      return b.type === a.type && b.key === a.key;
    case "calls":
    case "sends":
      return b.type === a.type && b.key === a.key && b.outcome === a.outcome;
  }
}
