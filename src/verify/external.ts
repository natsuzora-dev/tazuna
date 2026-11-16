import { z } from "zod";
import { tolerant } from "../data/canonical.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
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
  type AssumptionMismatch,
  assumptionMismatch,
  contractsListing,
  type ResultOfMismatch,
  rejectionKinds,
  resultOfMismatch,
} from "../syntax/structure.ts";
import { byLine, type Found, lineSchema } from "./lines.ts";

type LineOf<T extends TraceLine["type"]> = Extract<TraceLine, { readonly type: T }>;

interface Request {
  readonly definition: AnyCommand | AnyQuery;
  readonly line: LineOf<"command" | "query">;
  accepted: boolean;
}

type RequestRef = { readonly requestId: string; readonly target: DefinitionRef };

/** An accepted command of the trace and its results so far, which its ensures check. */
interface Accepted {
  readonly target: AnyCommand;
  readonly request: RequestRef;
  readonly results: { readonly input: unknown; readonly output?: unknown; readonly events: Emit[] };
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
    requests.set(l.id, definition === undefined ? undefined : { definition, line: l, accepted: false });
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
    if (l.answer.result === "rejected") {
      const target = refOfDefinition(spec, request.definition);
      return rejectionKinds(spec.structure, service, target).includes(l.answer.rejection.kind)
        ? { at, line: l, request }
        : ({
            kind: "Mismatch.unlistedRejectionKind",
            definition: null,
            line: at,
            data: { requestId: l.to, target, rejection: l.answer.rejection },
          } satisfies Mismatch);
    }
    request.accepted = l.answer.result === "accepted";
    return { at, line: l, request };
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
    if (request === undefined) return undefined;
    const target = refOfDefinition(spec, request.definition);
    const mismatch = resultOfMismatch(spec.structure, target, request.accepted, refOfDefinition(spec, event));
    return mismatch === undefined
      ? { at, line: l, event }
      : ({
          kind: resultOfKinds[mismatch],
          definition: null,
          line: at,
          data: { event: refOfDefinition(spec, event), requestId: l.resultOf, target },
        } satisfies Mismatch | Uncomparable);
  }
  return undefined;
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
  return { found, resolved };
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

function assumptionFinding(line: number, request: RequestRef, m: AssumptionMismatch): Mismatch {
  switch (m.kind) {
    case "rejectedAssumedRequires":
      return { kind: "Mismatch.rejectedAssumedRequires", definition: null, line, data: { ...request } };
    case "failedAssumedRequires":
      return {
        kind: "Mismatch.failedAssumedRequires",
        definition: null,
        line,
        data: { ...request, condition: m.condition },
      };
    case "failedAssumedEnsures":
      return {
        kind: "Mismatch.failedAssumedEnsures",
        definition: null,
        line,
        data: { ...request, condition: m.condition },
      };
  }
}

/**
 * Runs checkExternal, and on the lines that it finds nothing on, the checks that need spec functions or Zod schemas.
 */
export function verifyExternal(spec: Spec, service: string, trace: readonly FileLine[]): Found[] {
  const { found, resolved } = checkExternal(spec, service, trace);
  const problems: Found[] = [...found];
  const results = new Map<string, Accepted>();
  const accept = (target: AnyCommand, request: RequestRef, decoded: Omit<Accepted["results"], "events">) => {
    const accepted = { target, request, results: { ...decoded, events: [] } };
    results.set(request.requestId, accepted);
    return accepted.results;
  };
  resolved.forEach((r): void => {
    const line = r.at;
    if ("request" in r) {
      const { definition, line: request } = r.request;
      const { answer } = r.line;
      const ref = { requestId: r.line.to, target: refOfDefinition(spec, definition) };
      const input = z.object(definition.input as Record<string, z.ZodType>).safeParse(request.input);
      const out =
        answer.result === "rejected" || definition.output === undefined
          ? undefined
          : parseKnown(z.object(definition.output as Record<string, z.ZodType>), answer.output);
      if (input.success) {
        const decoded = { input: input.data, ...(out?.success === true ? { output: out.data } : {}) };
        const failedRequires = assumedRequires(definition, input.data);
        const failedEnsures =
          answer.result === "rejected" || failedRequires !== undefined || out?.success === false
            ? undefined
            : assumedEnsures(definition, definition.kind === "command" ? accept(definition, ref, decoded) : decoded);
        const broken = assumptionMismatch(answer, failedRequires, failedEnsures);
        if (broken !== undefined) problems.push(assumptionFinding(line, ref, broken));
      }
      if (out?.success === false)
        problems.push({
          kind: "Mismatch.answerOutputSchema",
          definition: null,
          line,
          data: { ...ref },
          error: zodError(out.error.issues),
        } satisfies Found & Mismatch);
      return;
    }
    const parsed = parseKnown(objectOf(r.event.payload), r.line.payload);
    if (!parsed.success) {
      problems.push({
        kind: "Mismatch.eventPayloadSchema",
        definition: null,
        line,
        data: { event: refOfDefinition(spec, r.event) },
        error: zodError(parsed.error.issues),
      } satisfies Found & Mismatch);
      return;
    }
    const accepted = r.line.resultOf === undefined ? undefined : results.get(r.line.resultOf);
    if (accepted === undefined) return;
    accepted.results.events.push(emit(r.event, parsed.data as never));
    const failed = assumedEnsures(accepted.target, accepted.results);
    if (failed !== undefined)
      problems.push(assumptionFinding(line, accepted.request, { kind: "failedAssumedEnsures", condition: failed }));
  });
  return problems.sort(byLine);
}
