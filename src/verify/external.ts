import type { Mismatch } from "../data/mismatch.generated.ts";
import type { Answer, TraceLine } from "../data/trace.generated.ts";
import { type FileLine, subjectOf } from "../data/trace.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { strictObjectOf } from "../data/values.ts";
import { zodError } from "../data/violation.ts";
import { type Conditions, firstFailing } from "../dsl/conditions.ts";
import type { AnyCommand, AnyEvent, AnyQuery, Emit } from "../dsl/definition.ts";
import { emit } from "../dsl/event.ts";
import type { Spec } from "../load/load.ts";
import { definitionOfTraceName, refOfDefinition } from "../load/traceName.ts";
import { firstFailedEnsures } from "../sim/spec/contract.ts";
import {
  assumptionMismatch,
  assumptionViolation,
  contractsListing,
  type ResultOfMismatch,
  rejectionKinds,
  resultOfMismatch,
} from "../spec/structure.ts";
import { comparedLines } from "./compare.ts";
import { byLine, type Found } from "./lines.ts";

/**
 * Lean's Exchange: a request that the external service received, the lines that send it again, and the answers and the
 * events naming it as their resultOf that later lines record, in trace order, each at its line. TS keeps the input and
 * payloads for verifyExternal.
 */
interface Exchange {
  readonly at: number;
  readonly resends: readonly number[];
  readonly id: string;
  readonly definition: AnyCommand | AnyQuery;
  readonly input: unknown;
  readonly answers: readonly { readonly at: number; readonly answer: Answer }[];
  readonly events: readonly EventLine[];
}

/** An event line whose name is an event of the service. */
interface EventLine {
  readonly at: number;
  readonly event: AnyEvent;
  readonly payload: unknown;
  readonly resultOf: string | undefined;
}

/** Returns the first requires of the target that fails on the input alone. */
const assumedRequires = (target: AnyCommand | AnyQuery, input: unknown): string | undefined =>
  firstFailing(target.requires as Conditions<unknown>, () => ({ input }));

const resultOfKinds = {
  resultOfNonCommand: "Uncomparable.resultOfNonCommand",
  resultOfUnacceptedRequest: "Mismatch.resultOfUnacceptedRequest",
  resultOfUnlistedEvent: "Mismatch.resultOfUnlistedEvent",
} as const satisfies Record<ResultOfMismatch, (Mismatch | Uncomparable)["kind"]>;

const isInRequest = (l: TraceLine): l is Extract<TraceLine, { readonly type: "command" | "query" }> =>
  l.dir === "in" && (l.type === "command" || l.type === "query");

/** The definition that a compared line names: a request's or an event's, looked up once per line. */
interface Named {
  readonly request?: AnyCommand | AnyQuery;
  readonly event?: AnyEvent;
}

function namedBy(spec: Spec, service: string, l: TraceLine | undefined): Named {
  if (l === undefined) return {};
  if (isInRequest(l)) {
    const request = definitionOfTraceName(spec, service, l.name, l.type);
    return request === undefined ? {} : { request };
  }
  if (l.dir !== "out" || l.type !== "event") return {};
  const event = definitionOfTraceName(spec, service, l.name, "event");
  return event === undefined ? {} : { event };
}

/** The event lines whose names are events of the service. */
const eventLines = (lines: readonly (TraceLine | undefined)[], named: readonly Named[]): EventLine[] =>
  lines.flatMap((l, i) => {
    const event = named[i]?.event;
    if (l?.dir !== "out" || l.type !== "event" || event === undefined) return [];
    return [{ at: i + 1, event, payload: l.payload, resultOf: l.resultOf }];
  });

/** Lean's exchanges: the requests that have a definition of the service, each with what later lines record of it. */
function exchanges(
  lines: readonly (TraceLine | undefined)[],
  named: readonly Named[],
  events: readonly EventLine[],
): Exchange[] {
  const sentWith = (id: string, l: TraceLine | undefined) => l !== undefined && isInRequest(l) && l.id === id;
  return lines.flatMap((l, i): Exchange[] => {
    const definition = named[i]?.request;
    if (l === undefined || !isInRequest(l) || definition === undefined) return [];
    if (lines.slice(0, i).some((e) => sentWith(l.id, e))) return [];
    const at = i + 1;
    const resends = lines.flatMap((r, j) => (j > i && sentWith(l.id, r) ? [j + 1] : []));
    const answers = lines.flatMap((a, j) =>
      j > i && a?.dir === "out" && a.type === "answer" && a.to === l.id ? [{ at: j + 1, answer: a.answer }] : [],
    );
    return [
      {
        at,
        resends,
        id: l.id,
        definition,
        input: l.input,
        answers,
        events: events.filter((e) => e.at > at && e.resultOf === l.id),
      },
    ];
  });
}

/**
 * Lean's checkLine: the violation of the line alone, which names `named`. `requests` are the ids of the earlier request
 * lines.
 */
function checkLine(
  spec: Spec,
  service: string,
  requests: ReadonlySet<string>,
  at: number,
  l: TraceLine,
  named: Named,
): Found | undefined {
  if (isInRequest(l))
    return named.request === undefined
      ? { kind: "Uncomparable.unknownRequest", definition: null, line: at, data: { subject: subjectOf(l) } }
      : undefined;
  if (l.dir === "out" && l.type === "answer")
    return requests.has(l.to)
      ? undefined
      : { kind: "Uncomparable.unknownAnswer", definition: null, line: at, data: { subject: subjectOf(l) } };
  if (l.dir !== "out" || l.type !== "event") return undefined;
  const { event } = named;
  if (event === undefined)
    return { kind: "Uncomparable.unknownEvent", definition: null, line: at, data: { subject: subjectOf(l) } };
  const ref = refOfDefinition(spec, event);
  if (l.resultOf === undefined)
    return contractsListing(spec.structure, ref).includes(service)
      ? undefined
      : { kind: "Mismatch.unlistedEvent", definition: null, line: at, data: { event: ref } };
  return requests.has(l.resultOf)
    ? undefined
    : {
        kind: "Uncomparable.resultOfUnknownRequest",
        definition: null,
        line: at,
        data: { event: ref, requestId: l.resultOf },
      };
}

/** Lean's checkAnswer: the violation of the answer `answer` at `at` to the request `x`. */
function checkAnswer(spec: Spec, service: string, x: Exchange, at: number, answer: Answer): Found | undefined {
  const request = { requestId: x.id, target: refOfDefinition(spec, x.definition) };
  if (answer.result === "rejected")
    return rejectionKinds(spec.structure, service, request.target).includes(answer.rejection.kind)
      ? undefined
      : assumptionViolation("Mismatch", request, { kind: "unlistedRejectionKind", rejection: answer.rejection }, at);
  return answer.result === (x.definition.kind === "command" ? "accepted" : "fulfilled")
    ? undefined
    : { kind: "Mismatch.answerResult", definition: null, line: at, data: { ...request, result: answer.result } };
}

/** Each answer of `x`, and whether it answers a send of `x` that no earlier answer answered (Lean's checkExchange). */
function answeringSends(x: Exchange): (Exchange["answers"][number] & { readonly answersSend: boolean })[] {
  let answered = 0;
  return x.answers.map((a) => {
    const answersSend = answered < 1 + x.resends.filter((r) => r < a.at).length;
    if (answersSend) answered += 1;
    return { ...a, answersSend };
  });
}

/**
 * Lean's checkExchange: the violations of the request `x`, of each answer that answers a send of it that no earlier
 * answer answered, of each other answer as repeated, and of each result event against the target and all the answers
 * (resultOfMismatch, as test checks them).
 */
function checkExchange(spec: Spec, service: string, x: Exchange): Found[] {
  const target = refOfDefinition(spec, x.definition);
  const answers = x.answers.map((a) => a.answer);
  return [
    ...answeringSends(x).map(({ at, answer, answersSend }): Found | undefined =>
      answersSend
        ? checkAnswer(spec, service, x, at, answer)
        : { kind: "Mismatch.repeatedAnswer", definition: null, line: at, data: { requestId: x.id, target } },
    ),
    ...x.events.map(({ at, event }): Found | undefined => {
      const mismatch = resultOfMismatch(spec.structure, target, answers, refOfDefinition(spec, event));
      return mismatch === undefined
        ? undefined
        : {
            kind: resultOfKinds[mismatch],
            definition: null,
            line: at,
            data: { event: refOfDefinition(spec, event), requestId: x.id, target },
          };
    }),
  ].filter((f) => f !== undefined);
}

/**
 * Lean's checkExternal: the violations of the lines that verify checks (comparedLines with in requests), by line,
 * followed by the violation of the line that ends them; and those lines' exchanges and event lines.
 */
export function checkExternal(
  spec: Spec,
  service: string,
  trace: readonly FileLine[],
): { found: Found[]; exchanges: Exchange[]; events: EventLine[] } {
  const { lines, cut } = comparedLines("in", trace);
  const named = lines.map((l) => namedBy(spec, service, l));
  const requests = new Set<string>();
  const found = lines.flatMap((l, i) => {
    if (l === undefined) return [];
    if (isInRequest(l)) requests.add(l.id);
    return checkLine(spec, service, requests, i + 1, l, named[i] ?? {}) ?? [];
  });
  const events = eventLines(lines, named);
  const exchanged = exchanges(lines, named, events);
  return {
    found: [
      ...[...found, ...exchanged.flatMap((x) => checkExchange(spec, service, x))].sort(byLine),
      ...(cut ? [cut] : []),
    ],
    exchanges: exchanged,
    events,
  };
}

/**
 * Runs checkExternal, and on the lines that it finds nothing on, the checks that need spec functions or Zod schemas:
 * each event's payload, and each answer that answers a send of its request: the request's input, which only a rejection
 * may answer when it fails the schema, and a command's ensures with all its result events, which may come before or
 * after the answer.
 */
export function verifyExternal(spec: Spec, service: string, trace: readonly FileLine[]): Found[] {
  const { found, exchanges, events } = checkExternal(spec, service, trace);
  const flagged = new Set(found.map((f) => f.line));
  const violations: Found[] = [...found];
  const emitted = new Map<number, Emit>();
  for (const { at, event, payload } of events) {
    if (flagged.has(at)) continue;
    const parsed = strictObjectOf(event.payload).safeParse(payload);
    if (parsed.success) emitted.set(at, emit(event, parsed.data as never));
    else
      violations.push({
        kind: "Mismatch.eventPayloadSchema",
        definition: null,
        line: at,
        data: { event: refOfDefinition(spec, event) },
        error: zodError(parsed.error.issues),
      } satisfies Found & Mismatch);
  }
  for (const x of exchanges) {
    const { definition } = x;
    const ref = { requestId: x.id, target: refOfDefinition(spec, definition) };
    const input = strictObjectOf(definition.input).safeParse(x.input);
    for (const { at: line, answer, answersSend } of answeringSends(x)) {
      if (!answersSend || flagged.has(line)) continue;
      const out =
        answer.result === "rejected" || definition.output === undefined
          ? undefined
          : strictObjectOf(definition.output).safeParse(answer.output);
      if (!input.success && answer.result !== "rejected")
        violations.push({
          kind: "Mismatch.requestInputSchema",
          definition: null,
          line,
          data: ref,
          error: zodError(input.error.issues),
        } satisfies Found & Mismatch);
      if (input.success) {
        const decoded = { input: input.data, ...(out?.success === true ? { output: out.data } : {}) };
        const failedRequires = assumedRequires(definition, input.data);
        const checked = answer.result !== "rejected" && failedRequires === undefined && out?.success !== false;
        const results = x.events.flatMap(({ at }) => emitted.get(at) ?? []);
        const withEvents = definition.kind === "command" ? { events: results } : {};
        const ensures = definition.ensures as Conditions<never>;
        const failedEnsures = checked ? firstFailedEnsures(ensures, { ...decoded, ...withEvents }) : undefined;
        const broken = assumptionMismatch(answer, failedRequires, failedEnsures);
        if (broken !== undefined) violations.push(assumptionViolation("Mismatch", ref, broken, line));
      }
      if (out?.success === false)
        violations.push({
          ...assumptionViolation("Mismatch", ref, { kind: "answerOutputSchema" }, line),
          error: zodError(out.error.issues),
        } satisfies Found & Mismatch);
    }
  }
  return violations.sort(byLine);
}
