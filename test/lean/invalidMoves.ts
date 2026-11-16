import type { StepName } from "../../src/data/choiceDependent.generated.ts";
import type { Answer } from "../../src/data/trace.generated.ts";
import type { Shape } from "../../src/data/values.ts";
import type { AnyCommand, AnyEvent, AnyQuery, AnyScreen, ChartSpec } from "../../src/dsl/definition.ts";
import type { Input } from "../../src/dsl/scenario.ts";
import { valuesFor } from "../../src/explore/values.ts";
import type { Spec } from "../../src/load/load.ts";
import type { Run } from "../../src/sim/spec/execute.ts";
import { contractsListing } from "../../src/syntax/structure.ts";

const malformed = "not an object";

const unlisted: Answer = { result: "rejected", rejection: { kind: "requires", reason: "unlisted" } };

/** The step of an automation that no spec defines, which the internal queue is never ready to take. */
const unready = (service: string): StepName => ({ kind: "reaction", automation: { service, name: "unready" } });

const controlsOf = (spec: Spec, service: string) =>
  spec.definitions.flatMap((d) =>
    d.service === service && d.definition.kind === "screen"
      ? Object.entries((d.definition as unknown as ChartSpec).controls ?? {}).map(([control, c]) => ({
          screen: d.definition as unknown as AnyScreen,
          control,
          shape: (c.payload ?? {}) as Shape,
        }))
      : [],
  );

/**
 * Returns the inputs at `time` that the spec rejects in every state: a malformed command, query, event, or control
 * payload, a command of another service, and an event outside the service's contracts.
 */
export function rejectedAnywhere(spec: Spec, service: string, time: string): Input[] {
  const of = <D>(
    kind: string,
    owned: (d: { readonly service: string; readonly name: string; readonly definition: unknown }) => boolean,
  ) => spec.definitions.find((d) => d.definition.kind === kind && owned(d))?.definition as D | undefined;
  const command = of<AnyCommand>("command", (d) => d.service === service);
  const query = of<AnyQuery>("query", (d) => d.service === service);
  const foreign = of<AnyCommand>("command", (d) => d.service !== service);
  const received = of<AnyEvent>("event", (d) => contractsListing(spec.structure, d).some((s) => s !== service));
  const outside = of<AnyEvent>("event", (d) => !contractsListing(spec.structure, d).some((s) => s !== service));
  const control = controlsOf(spec, service)[0];
  return [
    ...(command === undefined ? [] : [{ type: "command", command, input: malformed, time } as const]),
    ...(query === undefined ? [] : [{ type: "query", query, input: malformed, time } as const]),
    ...(foreign === undefined ? [] : [{ type: "command", command: foreign, input: {}, time } as const]),
    ...(received === undefined ? [] : [{ type: "event", event: received, payload: malformed, time } as const]),
    ...(outside === undefined ? [] : [{ type: "event", event: outside, payload: {}, time } as const]),
    ...(control === undefined
      ? []
      : [
          {
            type: "operation",
            screen: control.screen,
            control: control.control,
            payload: malformed,
            time,
          } as const,
        ]),
  ];
}

/**
 * Returns the inputs that the run reports in its current state: a time earlier than now, the end of a subscription that
 * is not open, a stale answer and an answer with an unlisted rejection reason to the first awaited request,
 * cannotOperate on the first enabled operation, an operation of a control that no enabled operation offers, and the
 * time and the first enabled input with a `stepOrder` that names a step the queue is never ready to take.
 */
export function invalidAfter(spec: Spec, service: string, run: Run, enabled: readonly Input[]): Input[] {
  const mock = enabled.find((input) => input.type === "answer");
  const offered = enabled.flatMap((input) => (input.type === "operation" ? [input] : []));
  const time = run.now.toString();
  const unoffered = controlsOf(spec, service).find(
    (c) => !offered.some((o) => o.screen === c.screen && o.control === c.control),
  );
  const payload = unoffered === undefined ? undefined : valuesFor(unoffered.shape, [], [], 1)[0];
  return [
    { type: "time", time: run.now.subtract({ milliseconds: 1 }).toString() },
    { type: "unsubscribe", to: "unopened", time },
    { type: "time", time, stepOrder: [unready(service)] },
    ...enabled.slice(0, 1).map((input) => ({ ...input, stepOrder: [unready(service)] })),
    ...(mock?.type === "answer" ? [{ ...mock, choice: { stale: true } } as const, { ...mock, answer: unlisted }] : []),
    ...offered.slice(0, 1).map((o) => ({ ...o, type: "unacceptedOperation" }) as const),
    ...(unoffered === undefined || payload === undefined
      ? []
      : [{ type: "operation", screen: unoffered.screen, control: unoffered.control, payload, time } as const]),
  ];
}
