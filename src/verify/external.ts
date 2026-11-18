import { z } from "zod";
import { tolerant } from "../data/canonical.ts";
import type { Mismatch } from "../data/mismatch.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { type FileLine, subjectOf, untilMalformed } from "../data/trace.ts";
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
import { byLine, type Found, lineSchema } from "./lines.ts";

type LineOf<T extends TraceLine["type"]> = Extract<TraceLine, { readonly type: T }>;

/** Lean's Request: a request of the trace, whether no answer rejected it, and the events naming it as resultOf. */
interface Request {
  readonly definition: AnyCommand | AnyQuery;
  readonly line: LineOf<"command" | "query">;
  accepted: boolean;
  answered: boolean;
  readonly results: { readonly at: number; readonly event: AnyEvent }[];
}

/** Returns the first requires of the target that fails on the input alone. */
const assumedRequires = (target: AnyCommand | AnyQuery, input: unknown): string | undefined =>
  firstFailing(target.requires as Conditions<unknown>, () => ({ input }));

/** A line that checkLine finds nothing on, and the request or event it resolved. */
type Resolved =
  | { readonly at: number; readonly line: LineOf<"answer">; readonly request: Request }
  | { readonly at: number; readonly line: LineOf<"event">; readonly event: AnyEvent };

const resultOfKinds = {
  resultOfNonCommand: "Uncomparable.resultOfNonCommand",
  resultOfUnacceptedRequest: "Mismatch.resultOfUnacceptedRequest",
  resultOfUnlistedEvent: "Mismatch.resultOfUnlistedEvent",
} as const satisfies Record<ResultOfMismatch, (Mismatch | Uncomparable)["kind"]>;

function checkLine(
  spec: Spec,
  service: string,
  requests: Map<string, Request | undefined>,
  at: number,
  l: TraceLine,
): Found | Resolved | undefined {
  if (l.dir === "in" && (l.type === "command" || l.type === "query")) {
    const definition = definitionOfTraceName(spec, service, l.name, l.type);
    requests.set(
      l.id,
      definition === undefined ? undefined : { definition, line: l, accepted: true, answered: false, results: [] },
    );
    return definition === undefined
      ? ({
          kind: "Uncomparable.unknownRequest",
          definition: null,
          line: at,
          data: { subject: subjectOf(l) },
        } satisfies Uncomparable)
      : undefined;
  }
  if (l.dir === "out" && l.type === "answer") {
    if (!requests.has(l.to))
      return {
        kind: "Uncomparable.unknownAnswer",
        definition: null,
        line: at,
        data: { subject: subjectOf(l) },
      } satisfies Uncomparable;
    const request = requests.get(l.to);
    if (request === undefined) return undefined;
    const target = refOfDefinition(spec, request.definition);
    if (request.answered)
      return {
        kind: "Mismatch.repeatedAnswer",
        definition: null,
        line: at,
        data: { requestId: l.to, target },
      } satisfies Mismatch;
    request.answered = true;
    request.accepted &&= l.answer.result === "accepted";
    if (l.answer.result === "rejected")
      return rejectionKinds(spec.structure, service, target).includes(l.answer.rejection.kind)
        ? { at, line: l, request }
        : assumptionViolation(
            "Mismatch",
            { requestId: l.to, target },
            { kind: "unlistedRejectionKind", rejection: l.answer.rejection },
            at,
          );
    return l.answer.result === (request.definition.kind === "command" ? "accepted" : "fulfilled")
      ? { at, line: l, request }
      : ({
          kind: "Mismatch.answerResult",
          definition: null,
          line: at,
          data: { requestId: l.to, target, result: l.answer.result },
        } satisfies Mismatch);
  }
  if (l.dir === "out" && l.type === "event") {
    const event = definitionOfTraceName(spec, service, l.name, "event");
    if (event === undefined)
      return {
        kind: "Uncomparable.unknownEvent",
        definition: null,
        line: at,
        data: { subject: subjectOf(l) },
      } satisfies Uncomparable;
    if (l.resultOf === undefined)
      return contractsListing(spec.structure, refOfDefinition(spec, event)).includes(service)
        ? { at, line: l, event }
        : ({
            kind: "Mismatch.unlistedEvent",
            definition: null,
            line: at,
            data: { event: refOfDefinition(spec, event) },
          } satisfies Mismatch);
    if (!requests.has(l.resultOf))
      return {
        kind: "Uncomparable.resultOfUnknownRequest",
        definition: null,
        line: at,
        data: { event: refOfDefinition(spec, event), requestId: l.resultOf },
      } satisfies Uncomparable;
    const request = requests.get(l.resultOf);
    request?.results.push({ at, event });
    return request === undefined ? undefined : { at, line: l, event };
  }
  return undefined;
}

/**
 * Lean's checkResults: the violations of the result events of the requests, found once the trace ends, since a result
 * event may come before or after its request's answer. A request that no answer reached may have results.
 */
function checkResults(spec: Spec, requests: ReadonlyMap<string, Request | undefined>): Found[] {
  return [...requests].flatMap(([requestId, request]) =>
    request === undefined
      ? []
      : request.results.flatMap(({ at, event }): Found[] => {
          const target = refOfDefinition(spec, request.definition);
          const mismatch = resultOfMismatch(spec.structure, target, request.accepted, refOfDefinition(spec, event));
          return mismatch === undefined
            ? []
            : [
                {
                  kind: resultOfKinds[mismatch],
                  definition: null,
                  line: at,
                  data: { event: refOfDefinition(spec, event), requestId, target },
                } satisfies Mismatch | Uncomparable,
              ];
        }),
  );
}

function checkLines(
  spec: Spec,
  service: string,
  lines: readonly (TraceLine | undefined)[],
): { found: Found[]; resolved: Resolved[] } {
  const found: Found[] = [];
  const resolved: Resolved[] = [];
  const requests = new Map<string, Request | undefined>();
  lines.forEach((l, i): void => {
    if (l === undefined) return;
    const checked = checkLine(spec, service, requests, i + 1, l);
    if (checked === undefined) return;
    if ("kind" in checked) found.push(checked);
    else resolved.push(checked);
  });
  const results = checkResults(spec, requests);
  const wrong = new Set(results.map((f) => f.line));
  return { found: [...found, ...results], resolved: resolved.filter((r) => !wrong.has(r.at)) };
}

/** Checks the lines before the trace's first malformed line, and then reports that line. */
export function checkExternal(
  spec: Spec,
  service: string,
  trace: readonly FileLine[],
): { found: Found[]; resolved: Resolved[] } {
  const { lines, malformed } = untilMalformed(trace);
  const { found, resolved } = checkLines(spec, service, lines);
  return { found: malformed === undefined ? found : [...found, lineSchema(malformed)], resolved };
}

const parseKnown = (schema: z.ZodType, value: unknown) => tolerant(schema).safeParse(value);

/**
 * Runs checkExternal, and on the lines that it finds nothing on, the checks that need spec functions or Zod schemas.
 * The answers are checked once the trace ends, a command's ensures with all its result events, which may come before
 * or after the answer.
 */
export function verifyExternal(spec: Spec, service: string, trace: readonly FileLine[]): Found[] {
  const { found, resolved } = checkExternal(spec, service, trace);
  const violations: Found[] = [...found];
  const results = new Map<string, Emit[]>();
  const answers: Extract<Resolved, { readonly request: Request }>[] = [];
  for (const r of resolved) {
    if ("request" in r) {
      answers.push(r);
      continue;
    }
    const parsed = parseKnown(objectOf(r.event.payload), r.line.payload);
    if (!parsed.success)
      violations.push({
        kind: "Mismatch.eventPayloadSchema",
        definition: null,
        line: r.at,
        data: { event: refOfDefinition(spec, r.event) },
        error: zodError(parsed.error.issues),
      } satisfies Found & Mismatch);
    else if (r.line.resultOf !== undefined)
      results.set(r.line.resultOf, [...(results.get(r.line.resultOf) ?? []), emit(r.event, parsed.data as never)]);
  }
  for (const { at: line, line: answerLine, request } of answers) {
    const { definition, line: requestLine } = request;
    const { answer } = answerLine;
    const ref = { requestId: answerLine.to, target: refOfDefinition(spec, definition) };
    const input = z.object(definition.input as Record<string, z.ZodType>).safeParse(requestLine.input);
    const out =
      answer.result === "rejected" || definition.output === undefined
        ? undefined
        : parseKnown(z.object(definition.output as Record<string, z.ZodType>), answer.output);
    if (input.success) {
      const decoded = { input: input.data, ...(out?.success === true ? { output: out.data } : {}) };
      const failedRequires = assumedRequires(definition, input.data);
      const checked = answer.result !== "rejected" && failedRequires === undefined && out?.success !== false;
      const events = definition.kind === "command" ? { events: results.get(answerLine.to) ?? [] } : {};
      const failedEnsures = checked ? assumedEnsures(definition, { ...decoded, ...events }) : undefined;
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
