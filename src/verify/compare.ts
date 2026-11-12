import { alike, Bag, matchCreated, Runs } from "../data/canonical.ts";
import type { Mismatch, Subject } from "../data/mismatch.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import {
  type Bindings,
  contentOf,
  type MalformedLine,
  type NumberedLine,
  nameOf,
  resultOf,
  sameTime,
  steps,
  toOf,
} from "../data/trace.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { plain } from "../data/values.ts";
import { type Found, lineSchema, resolveAfters } from "./lines.ts";

const json = (value: unknown) => JSON.stringify(value);

const subjectOf = (l: TraceLine): Subject =>
  l.type === "answer" || l.type === "unsubscribe"
    ? { type: l.type, to: l.to }
    : { type: l.type, name: nameOf(l) ?? null, id: l.id ?? null };

class Ids {
  private readonly bound = new Map<string, string>();
  private readonly taken = new Set<string>();
  private readonly groups = new Map<string, ReadonlySet<string>>();

  group(snapshot: readonly string[], trace: readonly string[]): void {
    if (snapshot.length === 1) this.bind(snapshot[0], trace[0]);
    else for (const id of snapshot) this.groups.set(id, new Set(trace));
  }

  matches(s: string | undefined, t: string | undefined): boolean {
    if (s === undefined || t === undefined) return s === t;
    const bound = this.bound.get(s);
    if (bound !== undefined) return bound === t;
    return this.groups.get(s)?.has(t) === true && !this.taken.has(t);
  }

  bind(s: string | undefined, t: string | undefined): void {
    if (s === undefined || t === undefined || this.bound.has(s)) return;
    this.bound.set(s, t);
    this.taken.add(t);
    this.groups.delete(s);
  }

  traceOf(s: string): string {
    return this.bound.get(s) ?? s;
  }
}

/** The violations of a comparison, and the bindings that it ends with. */
export interface Compared {
  readonly found: Found[];
  readonly bindings: Bindings;
}

/**
 * Compares the snapshot's lines with the trace's lines, and returns the violations and the bindings. `lines` are the
 * trace lines before its first malformed line `malformed`, and the window of that line is not compared. An unknown
 * after of the snapshot orders no line; readSnapshotProblems reports it before the comparison.
 */
export function compare(
  snapshot: readonly (TraceLine | undefined)[],
  lines: readonly (TraceLine | undefined)[],
  malformed: MalformedLine | undefined,
  internal: (l: TraceLine) => boolean,
): Compared {
  const problems: (Mismatch | Uncomparable)[] = [];
  const expected = steps(snapshot);
  const actual = steps(lines);
  const requestsById = new Map(snapshot.flatMap((l) => (l?.id === undefined ? [] : [[l.id, l] as const])));
  const ids = new Ids();
  const bindings = new Map<string, Set<string>>();
  const declared = new Set<string>();
  const substitute = (value: unknown): unknown => {
    if (typeof value === "string") return [...(bindings.get(value) ?? [])][0] ?? value;
    if (value instanceof Bag) return new Bag(value.items.map(substitute));
    if (value instanceof Runs) return new Runs(value.runs.map((r) => substitute(r) as Bag));
    if (Array.isArray(value)) return value.map(substitute);
    if (value && typeof value === "object")
      return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, substitute(v)]));
    return value;
  };
  const copyOf = (map: Map<string, Set<string>>) => new Map([...map].map(([k, v]) => [k, new Set(v)]));
  const mentionsKey = (s: unknown): boolean => {
    if (typeof s === "string") return declared.has(s);
    if (s instanceof Bag) return s.items.some(mentionsKey);
    if (s instanceof Runs) return s.runs.some(mentionsKey);
    return s !== null && typeof s === "object" && Object.values(s).some(mentionsKey);
  };
  /**
   * Returns whether `w` already stands for a snapshot value other than `v`. A value stands for one snapshot value, so
   * an implementation key that equals another snapshot value is not taken as that value.
   */
  const standsForOther = (map: Map<string, Set<string>>, v: string, w: string): boolean =>
    [...map].some(([k, ws]) => k !== v && ws.has(w));
  const bind = (s: unknown, t: unknown, map: Map<string, Set<string>> = bindings): void => {
    matchCreated(
      s,
      t,
      (v) => declared.has(v) && !map.has(v),
      (v, w) => {
        if (typeof w === "string" && !standsForOther(map, v, w)) map.set(v, new Set([w]));
      },
    );
  };
  const equal = (s: unknown, t: unknown, map: Map<string, Set<string>> = bindings, inInputLine = false): boolean => {
    if (typeof s === "string" && map.has(s)) {
      const same = map.get(s) as Set<string>;
      if (same.has(t as string)) return true;
      if (inInputLine && t === s && !standsForOther(map, s, s)) {
        same.add(s);
        return true;
      }
      return false;
    }
    if (s instanceof Runs) return t instanceof Runs && equal(s.runs, t.runs, map, inInputLine);
    if (s instanceof Bag) {
      const matched = t instanceof Bag ? matchBag(s.items, t.items, map, inInputLine) : undefined;
      if (matched === undefined) return false;
      // `matched` is `map` itself, or a copy of `map` with more bindings.
      for (const [k, v] of matched) map.set(k, v);
      return true;
    }
    if (Array.isArray(s))
      return Array.isArray(t) && s.length === t.length && s.every((v, i) => equal(v, t[i], map, inInputLine));
    if (s && typeof s === "object") {
      if (!t || typeof t !== "object" || Array.isArray(t)) return false;
      const ks = Object.keys(s);
      return (
        json(ks.toSorted()) === json(Object.keys(t).toSorted()) &&
        ks.every((k) => equal((s as Record<string, unknown>)[k], (t as Record<string, unknown>)[k], map, inInputLine))
      );
    }
    return s === t;
  };
  /**
   * Returns the bindings under which each of `ss` equals a distinct one of `ts`, or undefined. Equal candidates lead to
   * the same result, so only one of them is tried.
   */
  const matchBag = (
    ss: readonly unknown[],
    ts: readonly unknown[],
    map: Map<string, Set<string>>,
    inInputLine: boolean,
  ): Map<string, Set<string>> | undefined => {
    if (ss.length !== ts.length) return undefined;
    if (ss.length === 0) return map;
    const [first, ...rest] = ss;
    const tried = new Set<string>();
    for (const [i, t] of ts.entries()) {
      if (tried.has(json(t))) continue;
      tried.add(json(t));
      const tentative = mentionsKey(first) ? copyOf(map) : map;
      bind(first, t, tentative);
      if (!equal(first, t, tentative, inInputLine)) continue;
      const matched = matchBag(rest, ts.toSpliced(i, 1), tentative, inInputLine);
      if (matched !== undefined) return matched;
    }
    return undefined;
  };
  const samePlace = (s: TraceLine, t: TraceLine): boolean =>
    "to" in s ? ids.matches(s.to, toOf(t)) : nameOf(t) === nameOf(s);
  const answersQuery = (to: string) => {
    const request = requestsById.get(to);
    return request?.type === "query" || request?.type === "subscribe";
  };
  const queryAnswer = (l: TraceLine) =>
    l.type !== "answer" ? undefined : l.answer.result === "fulfilled" ? l.answer.output : l.answer;
  const compared = (s: TraceLine, t: TraceLine): readonly [unknown, unknown] =>
    s.type === "answer" && answersQuery(s.to) ? [queryAnswer(s), queryAnswer(t)] : [contentOf(s), contentOf(t)];

  const matchLine = (s: TraceLine, t: NumberedLine) => {
    const at = t.at;
    const actualLine = t.line;
    if (!sameTime(s, actualLine))
      problems.push({
        kind: "Mismatch.time",
        definition: null,
        data: { line: at, subject: subjectOf(actualLine), snapshot: s.time, trace: actualLine.time },
      });
    if (s.type === "answer") ids.bind(s.to, toOf(actualLine));
    const [expectedValue, actualValue] = compared(s, actualLine);
    bind(expectedValue, actualValue);
    if (equal(expectedValue, actualValue)) return;
    const got = plain(contentOf(actualLine));
    if (s.type === "command" || s.type === "query") {
      problems.push({
        kind: "Mismatch.request",
        definition: null,
        data: {
          line: at,
          id: actualLine.id ?? null,
          type: s.type,
          name: s.name,
          snapshot: plain(substitute(s.input)),
          trace: got,
        },
      });
      return;
    }
    if (s.type === "event") {
      problems.push({
        kind: "Mismatch.event",
        definition: null,
        data: { line: at, name: s.name, snapshot: plain(substitute(s.payload)), trace: got },
      });
      return;
    }
    if (s.type !== "answer" || actualLine.type !== "answer") return;
    const e = s.answer;
    const a = actualLine.answer;
    const to = actualLine.to;
    const output = (snapshot: unknown, trace: unknown): Mismatch => ({
      kind: "Mismatch.output",
      definition: null,
      data: { line: at, to, snapshot: plain(substitute(snapshot)), trace: plain(trace) },
    });
    if (answersQuery(s.to)) problems.push(output(queryAnswer(s), queryAnswer(actualLine)));
    else if (e.result !== a.result)
      problems.push({
        kind: "Mismatch.result",
        definition: null,
        data: { line: at, to, snapshot: e.result, trace: a.result },
      });
    else if (e.result === "rejected" && a.result === "rejected")
      problems.push({
        kind: "Mismatch.rejection",
        definition: null,
        data: { line: at, to, snapshot: e.rejection.kind, trace: a.rejection.kind },
      });
    else if (e.result === "accepted" && a.result === "accepted") problems.push(output(e.output, a.output));
  };

  const { follows } = resolveAfters(snapshot);

  const missing = (s: NumberedLine, line: number): Mismatch =>
    s.line.type === "answer" || s.line.type === "unsubscribe"
      ? {
          kind: "Mismatch.missingAnswer",
          definition: null,
          data: { line, type: s.line.type, to: ids.traceOf(s.line.to), snapshotLine: s.at },
        }
      : {
          kind: "Mismatch.missingLine",
          definition: null,
          data: {
            line,
            type: s.line.type,
            name: nameOf(s.line) as string,
            content: plain(substitute(contentOf(s.line))),
            snapshotLine: s.at,
          },
        };

  const isRequest = (l: TraceLine) => l.type === "command" || l.type === "query";

  const pairExactly = (
    ss: readonly NumberedLine[],
    ts: readonly NumberedLine[],
    map: Map<string, Set<string>>,
  ): { pairs: { spec: NumberedLine; trace: NumberedLine }[]; map: Map<string, Set<string>> } | undefined => {
    const [first, ...rest] = ss;
    if (first === undefined) return { pairs: [], map };
    const tried = new Set<string>();
    for (const [i, t] of ts.entries()) {
      if (t.line.type !== first.line.type || !samePlace(first.line, t.line) || !sameTime(first.line, t.line)) continue;
      const [expectedValue, actualValue] = compared(first.line, t.line);
      const text = json([toOf(t.line), actualValue]);
      if (tried.has(text)) continue;
      tried.add(text);
      const tentative = mentionsKey(expectedValue) ? copyOf(map) : map;
      bind(expectedValue, actualValue, tentative);
      if (!equal(expectedValue, actualValue, tentative)) continue;
      const paired = pairExactly(rest, ts.toSpliced(i, 1), tentative);
      if (paired !== undefined) return { pairs: [{ spec: first, trace: t }, ...paired.pairs], map: paired.map };
    }
    return undefined;
  };

  const pairForReport = (
    ss: readonly NumberedLine[],
    ts: readonly NumberedLine[],
    missingAt: number,
  ): { spec: NumberedLine; trace: NumberedLine }[] => {
    const used = new Set<NumberedLine>();
    const pairs: { spec: NumberedLine; trace: NumberedLine }[] = [];
    for (const s of ss) {
      const candidates = ts.filter((t) => !used.has(t) && t.line.type === s.line.type && samePlace(s.line, t.line));
      const sameContent = (t: NumberedLine) => {
        const [expectedValue, actualValue] = compared(s.line, t.line);
        const tentative = copyOf(bindings);
        bind(expectedValue, actualValue, tentative);
        return equal(expectedValue, actualValue, tentative);
      };
      const t =
        candidates.find((c) => sameContent(c) && sameTime(s.line, c.line)) ??
        candidates.find(sameContent) ??
        candidates[0];
      if (t === undefined) problems.push(missing(s, missingAt));
      else {
        used.add(t);
        pairs.push({ spec: s, trace: t });
        matchLine(s.line, t);
      }
    }
    return pairs;
  };

  const pairLines = (
    ss: readonly NumberedLine[],
    ts: readonly NumberedLine[],
    missingAt: number,
  ): { spec: NumberedLine; trace: NumberedLine }[] => {
    const exact = pairExactly(ss, ts, bindings);
    if (exact === undefined) return pairForReport(ss, ts, missingAt);
    for (const [k, v] of exact.map) bindings.set(k, v);
    for (const p of exact.pairs) matchLine(p.spec.line, p.trace);
    return exact.pairs;
  };

  const pairWindow = (
    ss: readonly NumberedLine[],
    ts: readonly NumberedLine[],
    missingAt: number,
  ): { spec: NumberedLine; trace: NumberedLine }[] => {
    const requests = pairLines(
      ss.filter((o) => isRequest(o.line)),
      ts,
      missingAt,
    );
    groupRequests(requests);
    const left = ts.filter((t) => !requests.some((p) => p.trace === t));
    return [
      ...requests,
      ...pairLines(
        ss.filter((o) => !isRequest(o.line)),
        left,
        missingAt,
      ),
    ];
  };

  type Open = Subscriptions<{ readonly line: Extract<TraceLine, { type: "subscribe" }>; readonly at: number }>;
  const openInSnapshot: Open = new Subscriptions();
  const openInTrace: Open = new Subscriptions();
  const idsOf = (open: Open) => open.entries().map(([id]) => id);
  const subscriptionIds = new Map<string, Set<string>>();
  const isSubscribing = (l: TraceLine) => l.type === "subscribe" || l.type === "unsubscribe";
  const follow = (open: Open, lines: readonly NumberedLine[]) => {
    for (const o of lines)
      if (o.line.type === "subscribe" && o.line.id !== undefined) open.subscribe(o.line.id, { line: o.line, at: o.at });
      else if (o.line.type === "unsubscribe") open.unsubscribe(o.line.to);
  };
  const pairOpen = (
    ss: readonly string[],
    ts: readonly string[],
    map: Map<string, Set<string>>,
  ): { pairs: (readonly [string, string])[]; map: Map<string, Set<string>> } | undefined => {
    const [first, ...rest] = ss;
    if (first === undefined) return ts.length === 0 ? { pairs: [], map } : undefined;
    const s = openInSnapshot.get(first);
    const tried = new Set<string>();
    for (const [i, id] of ts.entries()) {
      const t = openInTrace.get(id);
      if (s === undefined || t === undefined || s.line.name !== t.line.name) continue;
      const [expectedInput, actualInput] = [contentOf(s.line), contentOf(t.line)];
      if (tried.has(json(actualInput))) continue;
      tried.add(json(actualInput));
      const tentative = mentionsKey(expectedInput) ? copyOf(map) : map;
      bind(expectedInput, actualInput, tentative);
      if (!equal(expectedInput, actualInput, tentative)) continue;
      const paired = pairOpen(rest, ts.toSpliced(i, 1), tentative);
      if (paired !== undefined) return { pairs: [[first, id], ...paired.pairs], map: paired.map };
    }
    return undefined;
  };
  const reportedMissing = new Set<string>();
  const reportedUnexpected = new Set<string>();
  const compareSubscriptions = (
    specOut: readonly NumberedLine[],
    traceOut: readonly NumberedLine[],
    missingAt: number,
  ) => {
    follow(openInSnapshot, specOut);
    follow(openInTrace, traceOut);
    const exact = pairOpen(idsOf(openInSnapshot), idsOf(openInTrace), bindings);
    const pairs = exact?.pairs ?? [];
    if (exact === undefined) {
      const unpaired = new Set(idsOf(openInTrace));
      for (const [id, s] of openInSnapshot.entries()) {
        const t = [...unpaired].find((u) => {
          const other = openInTrace.get(u)?.line;
          return (
            other !== undefined &&
            other.name === s.line.name &&
            equal(contentOf(s.line), contentOf(other), copyOf(bindings))
          );
        });
        if (t !== undefined) {
          unpaired.delete(t);
          pairs.push([id, t]);
        } else if (!reportedMissing.has(id)) {
          reportedMissing.add(id);
          problems.push({
            kind: "Mismatch.unopenedSubscription",
            definition: null,
            data: {
              line: missingAt,
              name: s.line.name,
              input: plain(substitute(contentOf(s.line))),
              snapshotLine: s.at,
            },
          });
        }
      }
      for (const id of unpaired) {
        const t = openInTrace.get(id);
        if (t === undefined || reportedUnexpected.has(id)) continue;
        reportedUnexpected.add(id);
        problems.push({
          kind: "Mismatch.unexpectedSubscription",
          definition: null,
          data: { line: t.at, name: t.line.name, input: plain(contentOf(t.line)), id },
        });
      }
    } else for (const [k, v] of exact.map) bindings.set(k, v);
    const lineOf = (s: string) => openInSnapshot.get(s)?.line as TraceLine;
    for (const [s] of pairs) {
      const ids = subscriptionIds.get(s) ?? new Set();
      for (const [other, t] of pairs) if (alike(lineOf(s), lineOf(other))) ids.add(t);
      subscriptionIds.set(s, ids);
    }
  };

  const compareWindow = (
    allSpecOut: readonly NumberedLine[],
    allTraceOut: readonly NumberedLine[],
    missingAt: number,
  ) => {
    for (const s of allSpecOut) for (const v of s.line.created ?? []) declared.add(v);
    compareSubscriptions(
      allSpecOut.filter((s) => isSubscribing(s.line)),
      allTraceOut.filter((t) => isSubscribing(t.line)),
      missingAt,
    );
    const specOut = allSpecOut.filter((s) => !isSubscribing(s.line));
    const traceOut = allTraceOut.filter((t) => !internal(t.line) && !isSubscribing(t.line));
    const pairs = pairWindow(
      specOut.filter((s) => !internal(s.line)),
      traceOut,
      missingAt,
    );
    for (const { spec: s, trace: t } of pairs) {
      const before = pairs.find((p) => p.trace.at > t.at && follows.get(s.at)?.has(p.spec.at) === true);
      if (before !== undefined)
        problems.push({
          kind: "Mismatch.lineOrder",
          definition: null,
          data: { line: t.at, subject: subjectOf(t.line), before: subjectOf(before.trace.line) },
        });
    }
    for (const t of traceOut)
      if (!pairs.some((p) => p.trace === t))
        problems.push({
          kind: "Mismatch.unexpectedLine",
          definition: null,
          data: { line: t.at, subject: subjectOf(t.line) },
        });
  };

  const groupRequests = (pairs: readonly { spec: NumberedLine; trace: NumberedLine }[]) => {
    const groups: { line: TraceLine; snapshot: string[]; trace: string[] }[] = [];
    for (const { spec: s, trace: t } of pairs) {
      if (s.line.id === undefined || t.line.id === undefined) continue;
      const found = groups.find((g) => alike(g.line, s.line));
      const group = found ?? { line: s.line, snapshot: [], trace: [] };
      if (found === undefined) groups.push(group);
      group.snapshot.push(s.line.id);
      group.trace.push(t.line.id);
    }
    for (const group of groups) ids.group(group.snapshot, group.trace);
  };

  const sameInput = (s: TraceLine, t: TraceLine): boolean => {
    if (s.type !== t.type || nameOf(s) !== nameOf(t) || !sameTime(s, t)) return false;
    if (s.type === "time" || s.type === "restart") return true;
    if (s.type === "unsubscribe") return ids.matches(s.to, toOf(t));
    if (s.type === "answer" && t.type === "answer")
      return (
        (subscriptionIds.get(s.to)?.has(t.to) ?? ids.matches(s.to, t.to)) && equal(s.answer, t.answer, bindings, true)
      );
    return ids.matches(resultOf(s), resultOf(t)) && equal(contentOf(s), contentOf(t), bindings, true);
  };

  const count = malformed === undefined ? Math.max(expected.length, actual.length) : actual.length - 1;
  for (let k = 0; k < count; k += 1) {
    const previous = actual[k - 1]?.input;
    compareWindow(expected[k]?.before ?? [], actual[k]?.before ?? [], previous === undefined ? 1 : previous.at);
    const s = expected[k]?.input;
    const t = actual[k]?.input;
    if (s === undefined && t === undefined) return { found: problems, bindings };
    if (s === undefined) {
      const { at, line } = t as NumberedLine;
      problems.push({ kind: "Uncomparable.unexpectedInput", definition: null, data: { line: at, input: plain(line) } });
      return { found: problems, bindings };
    }
    if (t === undefined) {
      problems.push({
        kind: "Uncomparable.missingInput",
        definition: null,
        data: { line: lines.length, input: plain(s.line), snapshotLine: s.at },
      });
      return { found: problems, bindings };
    }
    if (!sameInput(s.line, t.line)) {
      problems.push(
        s.line.type === "answer" && t.line.type === "answer" && !ids.matches(s.line.to, t.line.to)
          ? {
              kind: "Uncomparable.answersNoRequest",
              definition: null,
              data: { line: t.at, to: t.line.to, snapshotLine: s.at },
            }
          : {
              kind: "Uncomparable.differentInput",
              definition: null,
              data: { line: t.at, snapshotLine: s.at, snapshot: plain(substitute(s.line)), trace: plain(t.line) },
            },
      );
      return { found: problems, bindings };
    }
    ids.bind(toOf(s.line), toOf(t.line));
    ids.bind(resultOf(s.line), resultOf(t.line));
    ids.bind(s.line.id, t.line.id);
  }
  return { found: malformed === undefined ? problems : [...problems, lineSchema(malformed)], bindings };
}
