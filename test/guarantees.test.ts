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

test("The theorems that docs/guarantees.md cites are the theorems tagged @[guarantee], and no others", () => {
  const doc = readFileSync(join(tests, "../docs/guarantees.md"), "utf8");
  const cited = [...new Set([...doc.matchAll(/`([a-z][A-Za-z0-9]*_\w*)`/g)].map((m) => m[1] ?? ""))];
  assert.deepEqual(difference(cited, guarantees), none);
});

/**
 * What runs a guarantee that has no fixture named after it: the example of a violation kind that the theorem states, a
 * scenario of another guarantee's fixture, or a reason. A fixture runs in TS and Lean, as every example does.
 */
type Instead =
  | { readonly kindExample: UserKind }
  | { readonly fixture: Guarantee; readonly scenario: string }
  | { readonly because: string };

const pending = { because: "fixture pending (P3b)" } as const;
const ofSort = {
  because:
    "a statement about sortCollections itself, over every value; collections.diff.ts compares the TS sort with Lean's on generated values",
} as const;
const ofCompare = {
  because:
    "a statement about verify's comparison itself; verify.diff.ts compares the TS and Lean comparisons on the example snapshots and on mutated traces",
} as const;
const ofRenaming = {
  because:
    "a property of the renaming relation, which the identity theorems use and no run computes, so no spec or trace can exercise it",
} as const;
const ofSearch = {
  because:
    "a statement about the step-order search and its outcome comparison; choiceDependent.diff.ts compares the TS and Lean searches on every example",
} as const;
const ofCheck = {
  because:
    "a statement about check over every structure; validation.diff.ts compares the TS and Lean check on every example spec, and each kind's example breaks one rule",
} as const;

const instead: Readonly<Partial<Record<Guarantee, Instead>>> = {
  accepted_command_writes_then_queues_reactions: pending,
  accepted_emits_decided: pending,
  always_rounds_limit_halts: { kindExample: "Fault.exceededAlwaysRounds" },
  ancestor_target_exits: pending,
  answerIn_agrees: pending,
  apart_disjoint: { kindExample: "Illegal.ambiguousUnion" },
  bag_or_set_array_sorted: ofSort,
  begin_agrees: pending,
  call_agrees: pending,
  canonical_check_eq_nil_iff: ofCheck,
  checkExchanges_agrees: pending,
  check_eq_nil_iff: ofCheck,
  chooseDeadline_stepOrder: pending,
  clock_publishes: { fixture: "changed_answer_sent", scenario: "answerChangesWithTime" },
  command_invalid_input_rejected: pending,
  command_limit_halts: { kindExample: "Fault.exceededCommandDepth" },
  compareSnapshot_eq_none_iff: {
    because:
      "a statement about test's snapshot comparison itself; verify.diff.ts compares it in TS and Lean on each example snapshot against a run of the same lines, and on mutated lines",
  },
  compareSnapshot_reordered: {
    because:
      "a statement about test's snapshot comparison itself; verify.diff.ts compares it in TS and Lean on each example snapshot against a run of the same lines, and on mutated lines",
  },
  compareTraces_ok: ofSearch,
  compare_matches: ofCompare,
  compose_fst_nodup: ofRenaming,
  compose_snd_nodup: ofRenaming,
  contentMatch_renamed: ofCompare,
  created_distinct: { fixture: "created_form", scenario: "createsKeys" },
  created_kept: pending,
  dangling_ref_reported_iff: { kindExample: "Fault.danglingRef" },
  deadline_message_at_its_time: { fixture: "fires_only_in_active_state", scenario: "deadlinePassed" },
  deadlines_exact: pending,
  decide_payloads_sorted: pending,
  difference_same: ofSearch,
  done_selections_limit_halts: { kindExample: "Fault.exceededOnDoneSelections" },
  drain_keeps_now: pending,
  due_deadlines_limit_halts: { kindExample: "Fault.exceededDueDeadlines" },
  endSubscription_agrees: pending,
  endWith_cancels_deadlines_and_requests: pending,
  ended_subscription_not_answered: pending,
  enters_initial: pending,
  entity_invariant_reported_iff: { kindExample: "Fault.failedEntityInvariant" },
  entryOrder_ancestors_first: {
    because:
      "a statement about the order that entryOrder computes for every state tree; microstep_enters_in_entry_order relates it to runs",
  },
  execute_agrees: pending,
  execute_keepsKeys: pending,
  execute_unwritten_not_created: pending,
  exitOrder_descendants_first: {
    because:
      "a statement about the order that exitOrder computes for every state tree; microstep_exits_in_exit_order relates it to runs",
  },
  exited_state_sends_nothing: pending,
  external_answer_needs_delivery: { kindExample: "InvalidScenario.notDelivered" },
  failed_ensures_blames_command: { kindExample: "Fault.failedEnsures" },
  fireDue_agrees: pending,
  first_answer_after_restart_kept: pending,
  group_lines_unordered: pending,
  halting_finding_stops: pending,
  halting_report_stops: pending,
  independent_unordered: pending,
  instrument_agrees: pending,
  invalid_input_answer_blames_sender: { kindExample: "Fault.inputSchema" },
  keyless_payload_reaches_all: { fixture: "keyed_payload_reaches_at_most_one", scenario: "eventWithoutKeyFields" },
  late_answer_written: pending,
  leave_makes_queued_stale: pending,
  leave_makes_requests_stale: pending,
  line_keeps_leftInFlight: pending,
  line_keeps_states: pending,
  lines_after_stop_ignored: pending,
  matchValue_renamed: ofCompare,
  matchValue_strRenamed: ofRenaming,
  message_keysDistinct: pending,
  message_outputs_at_its_time: pending,
  message_work_limit_halts: { kindExample: "Fault.exceededMessageWork" },
  microstep_enters_in_entry_order: { fixture: "microstep_exits_in_exit_order", scenario: "intoRegion" },
  modal_child_covers: { kindExample: "InvalidInput.coveredByModal" },
  moving_line_keeps_others: pending,
  no_violation_iff: {
    because:
      "a statement about pairing a traces folder with the scenarios; verify.diff.ts compares the TS and Lean pairing on the examples and on random trace and snapshot folders",
  },
  only_clock_moves_time: pending,
  operate_agrees: pending,
  ordered_same_channel: pending,
  overtaking_delivery_halts: { kindExample: "InvalidScenario.overtaking" },
  publish_agrees: pending,
  query_answered_again: { fixture: "resent_command_gets_first_answer", scenario: "askedTwice" },
  query_invalid_input_rejected: pending,
  receive_agrees: pending,
  redelivered_event_not_processed: { fixture: "resent_command_gets_first_answer", scenario: "redelivered" },
  reenter_false_not_exited: pending,
  refuse_answers_unavailable: pending,
  rejected_command_changes_nothing: pending,
  renamed_refl: ofRenaming,
  renamed_symm: ofRenaming,
  renamed_trans: ofRenaming,
  requirements_lookup: {
    because:
      "a statement about the requirements table that Service.ofStructure builds, which the other theorems take as a hypothesis and every example builds",
  },
  resolve_output_answered: pending,
  restart_agrees: pending,
  restart_forgets: {
    because:
      "states that a restart's result does not depend on the state it discards, which compares two runs that no fixture holds; restart_keeps runs the restart",
  },
  reused_id_rejected: { fixture: "resent_command_gets_first_answer", scenario: "changedInput" },
  sameState_renamed: ofCompare,
  select_follows_leaves: { fixture: "leaf_selects_innermost", scenario: "leftRegionWins" },
  select_picked_by_leaf: { fixture: "leaf_selects_innermost", scenario: "rightRegionWins" },
  send_agrees: pending,
  send_keysDistinct: pending,
  service_invariant_reported_iff: { kindExample: "Fault.failedServiceInvariant" },
  simulate_agrees: pending,
  simulate_records_perm: pending,
  simulate_reported: pending,
  sortByKey_equal_keys_in_canonical_order: ofSort,
  sortByKey_perm: ofSort,
  sortCanonical_perm: ofSort,
  sorting_resolve_parsed: pending,
  stale_answer_ignored: pending,
  stale_command_answer_ignored: pending,
  stepOrderSearch_same: ofSearch,
  stopped_machine_takes_no_event: pending,
  stopped_run_skips_exchanges: pending,
  subscribe_agrees: pending,
  then_only_reports: pending,
  unchanged_answer_not_sent: { fixture: "changed_answer_sent", scenario: "subscribed" },
  unlisted_emitted_event_halts: { kindExample: "Fault.unlistedEmittedEvent" },
  untaken_operation_changes_nothing: pending,
  unwritten_not_created: pending,
};

/** The folders under test whose name is a guarantee, each with the guarantee. */
const named = (dir: string): readonly (readonly [Guarantee, string])[] =>
  readdirSync(dir, { withFileTypes: true })
    .filter((e) => e.isDirectory() && !["node_modules", ".fixtures", "__snapshots__"].includes(e.name))
    .flatMap((e) => {
      const path = join(dir, e.name);
      return isGuarantee(e.name) ? [[e.name, path] as const] : named(path);
    });
const fixtures = named(tests);
const fixtureOf = new Map(fixtures);

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

test("Each entry in instead that names a kind names one with an example, and each that names a fixture names one of its scenarios", () => {
  const examples = new Set(exampleFolders().map(([kind]) => kind));
  assert.deepEqual(
    Object.entries(instead).filter(([, i]) => {
      if ("kindExample" in i) return !examples.has(i.kindExample);
      if ("fixture" in i) {
        const dir = fixtureOf.get(i.fixture);
        return dir === undefined || !existsSync(dir) || !hasScenario(dir, i.scenario);
      }
      return false;
    }),
    [],
  );
});
