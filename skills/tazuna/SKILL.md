---
name: tazuna
description: Write tazuna specs and scenarios and fix the violations that the tazuna CLI reports. Use when a project depends on @natsuzora-dev/tazuna, or when asked to specify a service, add a scenario, or fix a tazuna violation.
---

# tazuna

## Read the installed version

The DSL changes between minor versions before 1.0.
Read the docs and the sample that ship with the installed package, in `node_modules/@natsuzora-dev/tazuna/`, and never those on GitHub:

- `node_modules/@natsuzora-dev/tazuna/docs/concepts.md` and `node_modules/@natsuzora-dev/tazuna/docs/guarantees.md`.
- The ToDo sample spec in `node_modules/@natsuzora-dev/tazuna/samples/todo/spec/`, as the model for file layout and every DSL form.
- The doc comment of each exported function, through the type definitions.

## Write in this order

1. The contract of each service: its entities, commands, queries, and events, as in `todo/contract.ts` of the sample.
2. The scenarios that state what the service does, as in `todo/scenarios.ts` of the sample.
3. The machines, screens, and automations that make the scenarios pass.

## Run the loop

Run `npx tazuna check <spec>` after each edit, until it reports no violation.
Then repeat these steps until `test` passes:

1. Run `npx tazuna test <spec> --depth <n>`, with the depth of the project's test script.
2. For the first violation line, run `npx tazuna explain <kind>` with its `kind`.
   The output names the side at fault.
3. Fix that side: the spec, the scenario, or the implementation.
4. Re-run only that scenario with `--only <service>/<name>`, from the violation's `scenario`.
5. Run `test` without `--only` to see that the fix broke no other scenario.

When `test` passes, run `npx tazuna verify <spec> <traces>` on the implementation's traces, and fix its violations the same way.

## Never do these

- Never weaken a scenario's Then, and never delete a scenario, to silence a violation.
  If the scenario is wrong, say why before you change it.
- Never run `test --update` before you read every `Mismatch` line that `test` reported.
  Run it only when each difference is one that your spec change intends, and then read the `git diff` of `__snapshots__`.
