---
name: tazuna
description: Write tazuna specs and scenarios, prove their invariants, and fix the violations and counterexamples that the tazuna CLI reports. Use when a project depends on @natsuzora-dev/tazuna, or when asked to specify a service, add a scenario, or fix a tazuna violation.
---

# tazuna

## Read the installed version

The DSL changes between minor versions before 1.0.
Read the docs and the sample that ship with the installed package, in `node_modules/@natsuzora-dev/tazuna/`, and never those on GitHub:

- `node_modules/@natsuzora-dev/tazuna/docs/concepts.md` and `node_modules/@natsuzora-dev/tazuna/docs/guarantees.md`.
- The ToDo sample spec in `node_modules/@natsuzora-dev/tazuna/samples/todo/spec/`, as the model for file layout and every DSL form.
- The doc comment of each exported function, through the type definitions.

## Write in this order

1. The contract of each service: its entities with their keys and invariants, as in `todo/data.ts` of the sample, and its commands, queries, and events with their callers, which `todo/contract.ts` lists.
2. The bounds of each service, as in `todo/bounds.ts`.
3. The scenarios that state what the service does, as in `todo/scenarios.ts`.
4. The machines, screens, and automations that make the scenarios pass.

## Run the loop

Run `npx tazuna check <spec>` after each edit, until it reports no violation.
A `Restricted` violation names the form to use instead.

Then repeat these steps until `test` passes:

1. Run `npx tazuna test <spec>`.
2. For the first violation line, run `npx tazuna explain <kind>` with its `kind`.
   The output's `fixedIn` names the side at fault.
3. Fix that side: the spec, the scenario, or the implementation.
4. Re-run only that scenario with `--only <service>/<name>`, from the violation's `scenario`.
5. Run `test` without `--only` to see that the fix broke no other scenario.

A new scenario has no snapshot until `test --update` writes its first one.

When `test` passes, run `npx tazuna prove <spec>`.
For each counterexample, decide which case it is:

- If a run can reach the counterexample's state, the behavior is wrong. Fix the spec, and add a scenario that reaches the state.
- If no run can reach it, state the fact that rules it out as an invariant, and say in your reply why every run keeps that fact.

An undecided property is no failure. Report its reason, and do not rewrite the spec only to make it decided.

When the implementation exists, run `npx tazuna generate <spec> <inputs>`, have its tests send each input with `drive`, and run `npx tazuna verify <spec> <traces> --coverage` on the traces that they write.
Fix each violation as in the `test` loop.

## Never do these

- Never weaken a scenario's Then, and never delete a scenario, to silence a violation.
  If the scenario is wrong, say why before you change it.
- Never run `test --update` before you read every `Mismatch` line that `test` reported.
  Update only when the new behavior is intended.
- Never add an invariant that no run keeps, to silence a counterexample.
  `test` and `verify` report a broken invariant as a `Fault`, so such an invariant fails there instead.
