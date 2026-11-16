import { Bag, Runs, searchLimit } from "./canonical.ts";
import type { Answer } from "./trace.generated.ts";
import { type Bindings, bind } from "./trace.ts";
import { canonicalJson } from "./values.ts";

const isObject = (v: unknown): v is Record<string, unknown> =>
  v !== null && typeof v === "object" && !Array.isArray(v) && !(v instanceof Bag) && !(v instanceof Runs);

const sameKeys = (s: Record<string, unknown>, t: Record<string, unknown>): boolean =>
  canonicalJson(Object.keys(s).toSorted()) === canonicalJson(Object.keys(t).toSorted());

/** Lean's Unequal. */
export type Unequal = "differ" | "searchLimit";

export type Unified = Bindings | Unequal;

/** Lean's unify. */
export function unify(created: ReadonlySet<string>, s: unknown, t: unknown, bs: Bindings): Unified {
  if (typeof s === "string") {
    if (typeof t !== "string") return "differ";
    if (created.has(s)) return bind(bs, s, t) ?? "differ";
    return t === s ? bs : "differ";
  }
  if (Array.isArray(s)) return Array.isArray(t) && s.length === t.length ? unifyList(created, s, t, bs) : "differ";
  if (s instanceof Runs)
    return t instanceof Runs && s.runs.length === t.runs.length ? unifyList(created, s.runs, t.runs, bs) : "differ";
  if (s instanceof Bag) {
    if (!(t instanceof Bag) || !bagFits(created, s.items, t.items)) return "differ";
    const found = unifyBag(created, s.items, t.items, bs, searchLimit);
    if ("bindings" in found) return found.bindings;
    return found.left === 0 ? "searchLimit" : "differ";
  }
  if (isObject(s)) {
    if (!isObject(t) || !sameKeys(s, t)) return "differ";
    return unifyList(
      created,
      Object.values(s),
      Object.keys(s).map((k) => t[k]),
      bs,
    );
  }
  return s === t ? bs : "differ";
}

/** Lean's unifyList and unifyFields. */
function unifyList(
  created: ReadonlySet<string>,
  xs: readonly unknown[],
  ys: readonly unknown[],
  bs: Bindings,
): Unified {
  let bindings: Unified = bs;
  for (const [i, x] of xs.entries()) {
    if (typeof bindings === "string") return bindings;
    bindings = unify(created, x, ys[i], bindings);
  }
  return bindings;
}

/** Lean's fits, fitsList and fitsFields. */
function fits(created: ReadonlySet<string>, s: unknown, t: unknown): boolean {
  if (typeof s === "string") return typeof t === "string" && (created.has(s) || t === s);
  const all = (xs: readonly unknown[], ys: readonly unknown[]) =>
    xs.length === ys.length && xs.every((x, i) => fits(created, x, ys[i]));
  if (Array.isArray(s)) return Array.isArray(t) && all(s, t);
  if (s instanceof Runs) return t instanceof Runs && all(s.runs, t.runs);
  if (s instanceof Bag) return t instanceof Bag && s.items.length === t.items.length;
  if (isObject(s)) return isObject(t) && sameKeys(s, t) && Object.keys(s).every((k) => fits(created, s[k], t[k]));
  return s === t;
}

/** Lean's bagFits. */
function bagFits(created: ReadonlySet<string>, ss: readonly unknown[], ts: readonly unknown[]): boolean {
  const fitting = ss.map((s) => ts.flatMap((t, k) => (fits(created, s, t) ? [k] : [])));
  const keys = fitting.map((ks) => ks.join(","));
  return keys.every((key, i) => keys.filter((k) => k === key).length <= (fitting[i] as number[]).length);
}

type Search = { readonly bindings: Bindings } | { readonly left: number };

/** Lean's unifyBag and unifyBagFrom. */
function unifyBag(
  created: ReadonlySet<string>,
  ss: readonly unknown[],
  ts: readonly unknown[],
  bs: Bindings,
  left: number,
): Search {
  if (ss.length !== ts.length) return { left };
  const [first, ...rest] = ss;
  if (ss.length === 0) return { bindings: bs };
  let tries = left;
  for (const [i, t] of ts.entries()) {
    if (tries === 0) return { left: 0 };
    tries -= 1;
    const once = unify(created, first, t, bs);
    if (once === "searchLimit") return { left: 0 };
    if (once === "differ") continue;
    const all = unifyBag(created, rest, ts.toSpliced(i, 1), once, tries);
    if ("bindings" in all) return all;
    tries = all.left;
  }
  return { left: tries };
}

export type Form = (value: unknown) => unknown;

/** Lean's unifyAnswer. */
export function unifyAnswer(
  created: ReadonlySet<string>,
  seen: Form,
  form: Form,
  bs: Bindings,
  b: Answer,
  a: Answer,
): Unified {
  if (b.result === "rejected" || a.result === "rejected")
    return b.result === "rejected" && a.result === "rejected" && b.rejection.kind === a.rejection.kind ? bs : "differ";
  if (b.result !== a.result) return "differ";
  const [x, y] = ["output" in b ? b.output : undefined, "output" in a ? a.output : undefined];
  return x === undefined || y === undefined ? (x === y ? bs : "differ") : unify(created, seen(x), form(y), bs);
}
