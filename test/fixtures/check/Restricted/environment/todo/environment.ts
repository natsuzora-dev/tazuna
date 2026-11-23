import { parseInstant } from "@natsuzora-dev/tazuna";

let added = 0;
var last = "";
const T = Temporal;
const M = Math;

export const record = (title: string) => {
  added += 1;
  const previous = last;
  last = title;
  return { added, previous };
};

export const sorted = (titles: readonly string[]) => titles.toSorted((a, b) => a.localeCompare(b));

export const formatted = (n: number) => new Intl.NumberFormat("ja-JP").format(n);

export const clocks = () => [T.Now.instant(), M.random(), parseInstant("2026-10-25T00:00:00Z")];

export const shown = (count: number, at: Date, title: string) => [
  count.toLocaleString(),
  at.toLocaleDateString(),
  at.toLocaleTimeString(),
  title.toLocaleUpperCase(),
  title.toLocaleLowerCase(),
];
