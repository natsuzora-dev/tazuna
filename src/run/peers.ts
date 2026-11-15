import { comparable } from "../data/canonical.ts";
import { type Problem, toProblem } from "../data/problem.ts";
import type { Step } from "../data/step.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { canonicalJson } from "../data/values.ts";
import type { Location } from "../data/violation.ts";
import type { Contract, Named } from "../dsl/definition.ts";
import { type ElsewhereInput, elsewhereInputs, type Scenario, timed, writtenPositions } from "../dsl/scenario.ts";
import type { Spec } from "../load/load.ts";
import { definitionOfTraceName } from "../load/traceName.ts";
import { serviceOf } from "../semantics/service/basic.ts";
import {
  type Origin,
  type PeerNormal,
  peerEvent,
  peerFindings,
  peerInputs,
  peerName,
} from "../semantics/system/peer.ts";
import { execute, inputsOf, type Run, stepsOf } from "./execute.ts";

/** The arguments of peerInputs for one peer of a scenario's run, with the scenario's elsewhere inputs to the peer. */
export interface PeerDerivation {
  readonly peer: string;
  readonly received: readonly string[];
  readonly state: readonly Step[];
  readonly elsewhere: readonly (readonly [number, Step])[];
  readonly written: readonly ElsewhereInput[];
}

const isMessage = (l: TraceLine) =>
  l.type === "command" || l.type === "query" || l.type === "subscribe" || l.type === "event";

/** Returns the service whose exported contract is `value`, which load checks (Malformed.unknownPeer). */
const contractService = (spec: Spec, value: object): string =>
  (spec.contracts.find((c) => c.value === value) as Contract).service;

/**
 * Returns the line count of the run before which the elsewhere input arrives: after the lines of the inputs before it
 * and the lines due by its time, and before the next input's line.
 */
function linesBefore(run: Run, { input, before }: ElsewhereInput): number {
  const { lines } = run.outcome;
  const start = before === 0 ? 0 : (run.inputLines[before - 1] as number) + 1;
  const end = run.inputLines[before] ?? lines.length;
  const time = Temporal.Instant.from(input.time);
  for (let j = start; j < end; j += 1)
    if (Temporal.Instant.compare(Temporal.Instant.from((lines[j] as TraceLine).time), time) > 0) return j;
  return end;
}

/**
 * Returns the peers of the scenario's run, the spec services other than its own that it messages, names in `given` or
 * `elsewhere`, or emits an event to that they receive, each with the arguments of peerInputs.
 */
export function peerDerivations(spec: Spec, scenario: Named<Scenario>, run: Run): PeerDerivation[] {
  const { given } = scenario.definition;
  const written = elsewhereInputs(scenario.definition).map((e) => ({ ...e, peer: contractService(spec, e.service) }));
  const named = new Set([...Object.keys(given), ...written.map((e) => e.peer)]);
  const others = [...spec.services]
    .filter(([name, s]) => name !== scenario.service && !s.definition.external)
    .map(([name]) => name);
  const received = new Map(others.map((peer) => [peer, serviceOf(spec.structure, peer).received]));
  const peers = others.filter(
    (peer) =>
      named.has(peer) ||
      run.outcome.lines.some(
        (l) =>
          (isMessage(l) && "name" in l && peerName(peer, l.name) !== undefined) ||
          peerEvent(scenario.service, received.get(peer) ?? [], new Map(), l) !== undefined,
      ),
  );
  return peers.map((peer) => {
    const state = given[peer];
    const stateInputs = state === undefined ? [] : timed({ inputs: state });
    const mine = written.filter((e) => e.peer === peer);
    const steps = stepsOf(spec, peer, [...stateInputs, ...mine.map((e) => e.input)]);
    return {
      peer,
      received: received.get(peer) ?? [],
      state: steps.slice(0, stateInputs.length),
      elsewhere: mine.map((e, i) => [linesBefore(run, e), steps[stateInputs.length + i] as Step] as const),
      written: mine,
    };
  });
}

/**
 * Returns the peer's form of an output or payload that verify compares (comparable), with its bags and runs. A value
 * that does not match its schema stays as it is.
 */
export function peerNormal(spec: Spec, peer: string): PeerNormal {
  return (name, value) => {
    const d = definitionOfTraceName(spec, peer, name, "query", "command", "event");
    const shape = d?.kind === "event" ? d.payload : d?.output;
    try {
      return comparable(shape, value);
    } catch {
      return value;
    }
  };
}

/**
 * Runs the peer on the inputs that peerInputs derives from the scenario's run `lines` and the peer's own run of them,
 * and returns the derived inputs, the peer's run, and, when it halted, the origin of the input that halted it with the
 * halting violation's kind. The derivation starts from an empty run of the peer and repeats until the inputs stop
 * changing: an input depends only on the peer's run of the inputs before it. `normal` is the peer's peerNormal.
 */
export function runPeer(
  spec: Spec,
  normal: PeerNormal,
  service: string,
  lines: readonly TraceLine[],
  d: PeerDerivation,
) {
  const derive = (peerLines: readonly TraceLine[]) =>
    peerInputs(normal, service, d.peer, d.received, d.state, d.elsewhere, lines, peerLines);
  let derived = derive([]);
  for (let round = 0; ; round += 1) {
    const run = execute(
      spec,
      d.peer,
      inputsOf(
        spec,
        d.peer,
        derived.map((i) => i.step),
      ),
    );
    const next = derive(run.outcome.lines);
    if (canonicalJson(next) === canonicalJson(derived)) {
      const { halted } = run;
      if (halted === undefined) return { derived, run, halted: undefined };
      // A run halts on the last input that it takes.
      const halting = derived[run.execution.inputs.length - 1] as (typeof derived)[number];
      return { derived, run, halted: [halting.origin, halted.kind] as const };
    }
    if (round > derived.length) throw new Error(`the inputs of the peer ${d.peer} do not settle`);
    derived = next;
  }
}

/** The check of a scenario's mocks of one peer: the peer's run of the derived inputs unless it halted, and the problems. */
export interface PeerCheck {
  readonly peer: string;
  readonly lines: readonly TraceLine[] | undefined;
  readonly problems: readonly Problem[];
}

/**
 * Checks the mocks that the scenario's run, which did not halt, takes from each of its peers (peerFindings). A problem
 * caused by a line of the run is located at the scenario's input whose processing wrote that line.
 */
export function checkPeers(spec: Spec, scenario: Named<Scenario>, run: Run): PeerCheck[] {
  const positions = writtenPositions(scenario.definition);
  const ref = { service: scenario.service, name: scenario.name };
  const at = (input: number | undefined): Location => ({
    file: scenario.place.file,
    line: scenario.place.line,
    ...(input === undefined ? {} : { input }),
  });
  const lines = run.outcome.lines;
  return peerDerivations(spec, scenario, run).map((d) => {
    const normal = peerNormal(spec, d.peer);
    const peerRun = runPeer(spec, normal, scenario.service, lines, d);
    const locationOf = (o: Origin): Location =>
      o.type === "line"
        ? at(positions[run.inputLines.findLastIndex((l) => l <= o.line)])
        : at(o.type === "elsewhere" ? d.written[o.index]?.position : undefined);
    const findings = peerFindings(normal, scenario.service, d.peer, lines, peerRun.run.outcome.lines, peerRun.halted);
    return {
      peer: d.peer,
      lines: peerRun.halted === undefined ? peerRun.run.outcome.lines : undefined,
      problems: findings.map(({ origin, violation }) => toProblem(violation, locationOf(origin), { scenario: ref })),
    };
  });
}
