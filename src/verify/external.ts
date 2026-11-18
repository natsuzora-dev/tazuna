import { z } from "zod";
import type { Mismatch } from "../data/mismatch.generated.ts";
import { tolerant } from "../data/schemaNode.ts";
import type { Answer, TraceLine } from "../data/trace.generated.ts";
import { type FileLine, subjectOf } from "../data/trace.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { objectOf } from "../data/values.ts";
import { zodError } from "../data/violation.ts";
import { type Conditions, firstFailing } from "../dsl/conditions.ts";
import type { AnyCommand, AnyEvent, AnyQuery, Emit } from "../dsl/definition.ts";
import { emit } from "../dsl/event.ts";
import type { Spec } from "../load/load.ts";
import { definitionOfTraceName, refOfDefinition } from "../load/traceName.ts";
import { assumedEnsures } from "../sim/spec/contract.ts";
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
 * Lean's Exchange: a request that the external service received, and the answers and the events naming it as their
 * resultOf that later lines record, in trace order, each at its line. TS keeps the input and payloads for verifyExternal.
 */
interface Exchange {
  readonly at: number;
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

/** The event lines whose names are events of `service`. */
const eventLines = (spec: Spec, service: string, lines: readonly (TraceLine | undefined)[]): EventLine[] =>
  lines.flatMap((l, i) => {
    if (l?.dir !== "out" || l.type !== "event") return [];
    const event = definitionOfTraceName(spec, service, l.name, "event");
    return event === undefined ? [] : [{ at: i + 1, event, payload: l.payload, resultOf: l.resultOf }];
  });

/** Lean's exchanges: the requests that have a definition of `service`, each with what later lines record of it. */
function exchanges(
  spec: Spec,
  service: string,
  lines: readonly (TraceLine | undefined)[],
  events: readonly EventLine[],
): Exchange[] {
  return lines.flatMap((l, i): Exchange[] => {
    if (l === undefined || !isInRequest(l)) return [];
    const definition = definitionOfTraceName(spec, service, l.name, l.type);
    if (definition === undefined) return [];
    const at = i + 1;
    const answers = lines.flatMap((a, j) =>
      j > i && a?.dir === "out" && a.type === "answer" && a.to === l.id ? [{ at: j + 1, answer: a.answer }] : [],
    );
    return [
      {
        at,
        id: l.id,
        definition,
        input: l.input,
        answers,
        events: events.filter((e) => e.at > at && e.resultOf === l.id),
      },
    ];
  });
}

/** Lean's checkLine: the violation of the line alone. `requests` are the ids of the earlier request lines. */
function checkLine(
  spec: Spec,
  service: string,
  requests: ReadonlySet<string>,
  at: number,
  l: TraceLine,
): Found | undefined {
  if (isInRequest(l))
    return definitionOfTraceName(spec, service, l.name, l.type) === undefined
      ? { kind: "Uncomparable.unknownRequest", definition: null, line: at, data: { subject: subjectOf(l) } }
      : undefined;
  if (l.dir === "out" && l.type === "answer")
    return requests.has(l.to)
      ? undefined
      : { kind: "Uncomparable.unknownAnswer", definition: null, line: at, data: { subject: subjectOf(l) } };
  if (l.dir !== "out" || l.type !== "event") return undefined;
  const event = definitionOfTraceName(spec, service, l.name, "event");
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

/**
 * Lean's checkExchange: the violations of the request `x`, of its first answer, of each later answer as repeated, and
 * of each result event against the target and all the answers (resultOfMismatch, as test checks them).
 */
function checkExchange(spec: Spec, service: string, x: Exchange): Found[] {
  const target = refOfDefinition(spec, x.definition);
  const [first, ...repeated] = x.answers;
  const answers = x.answers.map((a) => a.answer);
  return [
    ...(first === undefined ? [] : [checkAnswer(spec, service, x, first.at, first.answer)]),
    ...repeated.map(
      ({ at }): Found => ({
        kind: "Mismatch.repeatedAnswer",
        definition: null,
        line: at,
        data: { requestId: x.id, target },
      }),
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
  const requests = new Set<string>();
  const found = lines.flatMap((l, i) => {
    if (l === undefined) return [];
    if (isInRequest(l)) requests.add(l.id);
    return checkLine(spec, service, requests, i + 1, l) ?? [];
  });
  const events = eventLines(spec, service, lines);
  const exchanged = exchanges(spec, service, lines, events);
  return {
    found: [
      ...[...found, ...exchanged.flatMap((x) => checkExchange(spec, service, x))].sort(byLine),
      ...(cut ? [cut] : []),
    ],
    exchanges: exchanged,
    events,
  };
}

const parseKnown = (schema: z.ZodType, value: unknown) => tolerant(schema).safeParse(value);

/**
 * Runs checkExternal, and on the lines that it finds nothing on, the checks that need spec functions or Zod schemas:
 * each event's payload, and each request's first answer, a command's ensures with all its result events, which may come
 * before or after the answer.
 */
export function verifyExternal(spec: Spec, service: string, trace: readonly FileLine[]): Found[] {
  const { found, exchanges, events } = checkExternal(spec, service, trace);
  const flagged = new Set(found.map((f) => f.line));
  const violations: Found[] = [...found];
  const emitted = new Map<number, Emit>();
  for (const { at, event, payload } of events) {
    if (flagged.has(at)) continue;
    const parsed = parseKnown(objectOf(event.payload), payload);
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
    const [first] = x.answers;
    if (first === undefined || flagged.has(first.at)) continue;
    const { definition } = x;
    const { at: line, answer } = first;
    const ref = { requestId: x.id, target: refOfDefinition(spec, definition) };
    const input = z.object(definition.input as Record<string, z.ZodType>).safeParse(x.input);
    const out =
      answer.result === "rejected" || definition.output === undefined
        ? undefined
        : parseKnown(z.object(definition.output as Record<string, z.ZodType>), answer.output);
    if (input.success) {
      const decoded = { input: input.data, ...(out?.success === true ? { output: out.data } : {}) };
      const failedRequires = assumedRequires(definition, input.data);
      const checked = answer.result !== "rejected" && failedRequires === undefined && out?.success !== false;
      const results = x.events.flatMap(({ at }) => emitted.get(at) ?? []);
      const withEvents = definition.kind === "command" ? { events: results } : {};
      const failedEnsures = checked ? assumedEnsures(definition, { ...decoded, ...withEvents }) : undefined;
      const broken = assumptionMismatch(answer, failedRequires, failedEnsures);
      if (broken !== undefined) violations.push(assumptionViolation("Mismatch", ref, broken, line));
    }
    if (out?.success === false)
      violations.push({
        ...assumptionViolation("Mismatch", ref, { kind: "answerOutputSchema" }, line),
        error: zodError(out.error.issues),
      } satisfies Found & Mismatch);
  }
  return violations.sort(byLine);
}
