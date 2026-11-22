import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { test } from "node:test";
import { exampleFolders } from "../scripts/explain.ts";
import type { UserKind } from "../src/data/kinds.ts";
import { groupExamples, runExamples, simExamples } from "./examples.ts";
import { type Guarantee, guarantees } from "./guarantees.generated.ts";

const tests = import.meta.dirname;
const isGuarantee = (name: string): name is Guarantee => guarantees.some((g) => g === name);

/** The names in `a` that `b` lacks, and the names in `b` that `a` lacks. */
const difference = (a: readonly string[], b: readonly string[]) => ({
  onlyFirst: a.filter((n) => !b.includes(n)).toSorted(),
  onlySecond: b.filter((n) => !a.includes(n)).toSorted(),
});
const none = { onlyFirst: [], onlySecond: [] };

const doc = readFileSync(join(tests, "../docs/guarantees.md"), "utf8");
const proven = doc.slice(doc.indexOf("## Proven properties"));
/** The last cell of each body row of the tables under Proven properties: the theorems that prove the row. */
const theoremCells = proven
  .split("\n")
  .filter((line) => line.startsWith("| ") && !line.startsWith("| Property |"))
  .map((line) => line.slice(0, -" |".length).split(" | ").at(-1) ?? "");

test("Proven properties is the last section of docs/guarantees.md, and the last cell of each of its rows lists theorems", () => {
  assert.ok(!proven.includes("\n## "));
  assert.ok(theoremCells.length > 0);
  assert.deepEqual(
    theoremCells.filter((cell) => !/^`\w+`(?:, `\w+`)*$/.test(cell)),
    [],
  );
});

test("The theorems in the last cells under Proven properties are the theorems tagged @[guarantee], and no others", () => {
  const cited = [...new Set(theoremCells.flatMap((cell) => [...cell.matchAll(/`(\w+)`/g)].map((m) => m[1] ?? "")))];
  assert.deepEqual(difference(cited, guarantees), none);
});

/**
 * What runs a guarantee that has no fixture named after it. A fixture runs in the engine, as every example does.
 *
 * - `kindExample`: the example of a violation kind that the theorem states.
 * - `example` and `scenario`: a scenario of an example, by its path under test, that exercises the theorem.
 * - `diffTest`: the file under test of the diff test that compares, in TS and Lean, the function that the theorem states
 *   over all its inputs, which no one run can show.
 * - `because`: why no run can exercise the theorem.
 */
type Instead =
  | { readonly kindExample: UserKind }
  | { readonly example: string; readonly scenario: string }
  | { readonly diffTest: string }
  | { readonly because: string };

const ofCompare = {
  because:
    "a property of verify's comparison over all traces, which the engine runs on every verify example; no one run shows all traces",
} as const;
const ofSort = { diffTest: "collections.diff.ts" } as const;
const ofSearch = {
  because:
    "a property of the step-order search over all executions, which the engine runs on every test example; no one run shows all executions",
} as const;
const ofCheck = {
  because:
    "a property of the structure check over all structures, which the engine runs on every check; no one run shows all structures",
} as const;
const ofExplored = {
  because:
    "a property of exploration over all paths, which the engine runs on every test example; no one run shows all paths",
} as const;
const ofRenaming = {
  because:
    "a property of the renaming relation, which the identity theorems use and no run computes, so no spec or trace can exercise it",
} as const;
const ofAudit = {
  because:
    "states that a run whose spec functions are instrumented equals the plain run; the engine runs instrumented, and no command runs the plain one",
} as const;
const network = (scenario: string) => ({ example: "sim/Run/network", scenario }) as const;

const instead: Readonly<Partial<Record<Guarantee, Instead>>> = {
  accepted_emits_decided: { example: "service/Records/decide_payloads_sorted", scenario: "listed" },
  always_rounds_limit_halts: { kindExample: "Fault.exceededAlwaysRounds" },
  always_step_independent: ofSearch,
  answerIn_agrees: ofAudit,
  apart_disjoint: { kindExample: "Illegal.ambiguousUnion" },
  bag_or_set_array_sorted: ofSort,
  begin_agrees: ofAudit,
  call_agrees: ofAudit,
  canonical_check_eq_nil_iff: ofCheck,
  checkExchanges_agrees: ofAudit,
  check_eq_nil_iff: ofCheck,
  clock_publishes: { example: "service/Query/changed_answer_sent", scenario: "answerChangesWithTime" },
  command_limit_halts: { kindExample: "Fault.exceededCommandDepth" },
  compareSnapshot_eq_none_iff: ofCompare,
  compareSnapshot_reordered: ofCompare,
  compareTraces_ok: ofSearch,
  compare_matches: ofCompare,
  compose_fst_nodup: ofRenaming,
  compose_snd_nodup: ofRenaming,
  contentMatch_renamed: ofCompare,
  created_distinct: { example: "sim/Run/created_form", scenario: "createsKeys" },
  created_kept: { example: "sim/Run/created_form", scenario: "createsKeys" },
  dangling_ref_reported_iff: { kindExample: "Fault.danglingRef" },
  deadline_message_at_its_time: { example: "service/Chart/Deadline/deadlines", scenario: "deadlinePassed" },
  deadlines_exact: { example: "service/Chart/Deadline/deadlines", scenario: "deadlinePassed" },
  difference_same: ofSearch,
  done_selections_limit_halts: { kindExample: "Fault.exceededOnDoneSelections" },
  drain_keeps_now: { example: "service/Chart/Deadline/deadlines", scenario: "deadlinePassed" },
  due_deadlines_limit_halts: { kindExample: "Fault.exceededDueDeadlines" },
  endSubscription_agrees: ofAudit,
  ended_subscription_not_answered: { example: "service/Restart/restart_keeps", scenario: "subscriptionsEnd" },
  enters_initial: { example: "service/Chart/Config/exit-transition-entry-order", scenario: "intoRegion" },
  entity_invariant_reported_iff: { kindExample: "Fault.failedEntityInvariant" },
  entryOrder_ancestors_first: {
    because:
      "a statement about the order that entryOrder computes for every state tree; microstep_enters_in_entry_order relates it to runs",
  },
  execute_agrees: ofAudit,
  execute_keepsKeys: { example: "sim/Run/created_form", scenario: "createsKeys" },
  execute_unwritten_not_created: { example: "sim/Run/keys", scenario: "givenKeyApart" },
  exitOrder_descendants_first: {
    because:
      "a statement about the order that exitOrder computes for every state tree; microstep_exits_in_exit_order relates it to runs",
  },
  explored_sent_ids_distinct: ofExplored,
  external_answer_needs_delivery: { kindExample: "InvalidScenario.notDelivered" },
  failed_ensures_blames_command: { kindExample: "Fault.failedEnsures" },
  fireDue_agrees: ofAudit,
  first_answer_after_restart_kept: ofCompare,
  halting_finding_stops: { kindExample: "Fault.emittedPayloadSchema" },
  halting_report_stops: network("linesAfterHalt"),
  independent_unordered: network("deliversIndependentEvents"),
  instrument_agrees: ofAudit,
  invalid_input_answer_blames_sender: { kindExample: "Fault.inputSchema" },
  keyless_payload_reaches_all: { example: "service/Chart/Select/map-copies-by-key", scenario: "eventWithoutKeyFields" },
  leave_makes_requests_stale: { example: "service/Chart/Request/requests-on-entry", scenario: "answerAfterExit" },
  line_keeps_leftInFlight: { example: "sim/Run/moving_line_keeps_others", scenario: "leavesInFlight" },
  line_keeps_states: { example: "sim/Run/moving_line_keeps_others", scenario: "leavesInFlight" },
  lines_after_stop_ignored: network("linesAfterHalt"),
  matchValue_renamed: ofCompare,
  matchValue_strRenamed: ofCompare,
  message_keysDistinct: { example: "service/Message/rejection-kinds", scenario: "commandRejections" },
  message_outputs_at_its_time: { example: "service/Chart/Deadline/deadlines", scenario: "deadlinePassed" },
  message_work_limit_halts: { kindExample: "Fault.exceededMessageWork" },
  microstep_enters_in_entry_order: {
    example: "service/Chart/Config/exit-transition-entry-order",
    scenario: "intoRegion",
  },
  merged_search_reports: {
    because:
      "a property of breadth-first search over any space whose fingerprint keeps what later paths report; run.diff.ts compares the fingerprint itself in TS and Lean",
  },
  modal_child_covers: { kindExample: "InvalidInput.coveredByModal" },
  moves_enabled: ofExplored,
  no_violation_iff: ofCompare,
  only_clock_moves_time: network("delivered"),
  operate_agrees: ofAudit,
  overtaking_delivery_halts: { kindExample: "InvalidScenario.overtaking" },
  post_message: { example: "service/Restart/requests", scenario: "requestsDiscarded" },
  publish_agrees: ofAudit,
  query_answered_again: { example: "service/Idempotency/same-id", scenario: "askedTwice" },
  query_invalid_input_rejected: { example: "service/Message/rejection-kinds", scenario: "queryRejections" },
  receive_agrees: ofAudit,
  redelivered_event_not_processed: { example: "service/Idempotency/same-id", scenario: "redelivered" },
  reenter_false_not_exited: { example: "service/Chart/Config/reenter_true_exits", scenario: "addedThrice" },
  refuse_answers_unavailable: network("refusesRequest"),
  rejected_command_changes_nothing: { example: "service/Message/rejection-kinds", scenario: "commandRejections" },
  renamed_refl: ofRenaming,
  renamed_symm: ofRenaming,
  renamed_trans: ofRenaming,
  requirements_lookup: {
    because:
      "a statement about the requirements table that Service.ofStructure builds, which the other theorems take as a hypothesis and every example builds",
  },
  resolve_output_answered: { example: "service/Records/sorted-by", scenario: "queried" },
  restart_agrees: ofAudit,
  restart_forgets: {
    because:
      "states that a restart's result does not depend on the state it discards, which compares two runs that no fixture holds; restart_keeps runs the restart",
  },
  reused_id_rejected: { example: "service/Idempotency/same-id", scenario: "changedInput" },
  sameState_renamed: ofCompare,
  select_follows_leaves: { example: "service/Chart/Select/leaf_selects_innermost", scenario: "leftRegionWins" },
  select_picked_by_leaf: { example: "service/Chart/Select/leaf_selects_innermost", scenario: "rightRegionWins" },
  send_agrees: ofAudit,
  send_keysDistinct: { example: "service/Message/rejection-kinds", scenario: "commandRejections" },
  sent_ids_distinct: { example: "service/Restart/requests", scenario: "requestsDiscarded" },
  service_invariant_reported_iff: { kindExample: "Fault.failedServiceInvariant" },
  simulate_agrees: ofAudit,
  simulate_records_perm: {
    because:
      "states that two runs whose Given writes the same records in other orders are alike, which compares two runs that no fixture holds",
  },
  simulate_reported: network("leftInFlight"),
  slots_complete: ofExplored,
  sortByKey_equal_keys_in_canonical_order: ofSort,
  sortByKey_perm: ofSort,
  sortCanonical_perm: ofSort,
  sorting_resolve_parsed: { example: "service/Records/sorted-by", scenario: "queried" },
  stale_answer_ignored: { example: "service/Chart/Request/requests-on-entry", scenario: "answerAfterExit" },
  stale_command_answer_ignored: {
    example: "service/Chart/Queue/leave_makes_queued_stale",
    scenario: "loggedBeforeAnswer",
  },
  start_sent_ids_distinct: { example: "service/Restart/requests", scenario: "requestsDiscarded" },
  start_unwritten_not_created: { example: "sim/Run/keys", scenario: "givenKeyApart" },
  stepOrderSearch_same: ofSearch,
  stopped_run_skips_exchanges: network("overtaking"),
  subscribe_agrees: ofAudit,
  then_only_reports: network("unmetExpectation"),
  unchanged_answer_not_sent: { example: "service/Query/changed_answer_sent", scenario: "subscribed" },
  uncovered_unreached: ofExplored,
  unlisted_emitted_event_halts: {
    because:
      "no spec that check passes emits an event that its command does not list, since the IR names only listed events; the theorem keeps the semantics total over every Functions",
  },
  unwritten_not_created: { example: "sim/Run/keys", scenario: "givenKeyApart" },
};

/**
 * The folders under test whose name is a guarantee, each with the guarantee. Such a fixture holds only scenarios that
 * exercise its guarantee, as a kind's example holds only that kind: a scenario of anything else, even one that an entry
 * in instead cites, lives in an example named for what it shows. No test can tell what a scenario exercises, so this
 * rule is checked by review.
 */
const named = (dir: string): readonly (readonly [Guarantee, string])[] =>
  readdirSync(dir, { withFileTypes: true })
    .filter((e) => e.isDirectory() && !["node_modules", ".fixtures", "__snapshots__"].includes(e.name))
    .flatMap((e) => {
      const path = join(dir, e.name);
      return isGuarantee(e.name) ? [[e.name, path] as const] : named(path);
    });
const fixtures = named(tests);

/** The examples that a diff test runs in TS and Lean. */
const diffed = new Set([
  ...runExamples(),
  ...simExamples().map((e) => e.root),
  ...groupExamples("load"),
  ...groupExamples("validation"),
  ...groupExamples("verify"),
]);

test("Each guarantee has one fixture, a diff-tested example named after its theorem, or else one entry in instead", () => {
  assert.deepEqual(
    guarantees.filter((g) => fixtures.filter(([f]) => f === g).length + (g in instead ? 1 : 0) !== 1),
    [],
  );
  assert.deepEqual(
    fixtures.filter(([, path]) => !diffed.has(path)).map(([, path]) => relative(tests, path)),
    [],
  );
});

const hasScenario = (dir: string, name: string): boolean =>
  readdirSync(dir, { withFileTypes: true }).some((e) =>
    e.isDirectory()
      ? hasScenario(join(dir, e.name), name)
      : e.name === `${name}.scenario.json` ||
        (e.name.endsWith(".ts") &&
          new RegExp(`^export const ${name} = scenario\\(`, "m").test(readFileSync(join(dir, e.name), "utf8"))),
  );

test("Each entry in instead that names a kind names one with an example, each that names an example names one of its scenarios, and each that names a diff test names a file of one", () => {
  const examples = new Set(exampleFolders().map(([kind]) => kind));
  assert.deepEqual(
    Object.entries(instead).filter(([, i]) => {
      if ("kindExample" in i) return !examples.has(i.kindExample);
      if ("example" in i) {
        const dir = join(tests, i.example);
        return !diffed.has(dir) || !hasScenario(dir, i.scenario);
      }
      if ("diffTest" in i) return !i.diffTest.endsWith(".diff.ts") || !existsSync(join(tests, i.diffTest));
      return false;
    }),
    [],
  );
});
