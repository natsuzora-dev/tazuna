# tazuna

tazuna is a language for specifying services in TypeScript.
A spec defines each service's records, commands, queries, events, machines, and screens, and its scenarios state what the service does.
tazuna turns the spec into data that Lean 4 defines the meaning of, and the `tazuna` command uses that meaning in five ways:

- `check` checks the spec without running it.
- `test` runs the scenarios and compares each run with its snapshot.
- `prove` proves the spec's invariants with the Z3 solver, or reports a counterexample.
- `generate` writes inputs that reach the parts of the spec that no scenario reaches.
- `verify` replays an implementation's traces and compares its outputs with the spec's.

Before 1.0, a minor version may break the DSL.
Read the docs and samples of the version you installed, in `node_modules/@natsuzora-dev/tazuna`, not those on GitHub.

## Install tazuna

1. Install tazuna, its peers `typescript` and `zod`, and `@types/node`:

   ```sh
   npm install -D @natsuzora-dev/tazuna typescript zod @types/node
   ```

   npm also installs tazuna's engine, a native binary, from the optional dependency that matches your platform, so you need no Lean toolchain.
   tazuna ships the engine for macOS on Apple silicon and Intel, Linux on arm64 and x64 with glibc, and Windows on x64.
   Keep optional dependencies installed, since tazuna has no engine to run without them.

2. Make your package an ES module package, since tazuna ships only ES modules:

   ```sh
   npm pkg set type=module
   ```

3. Create a `tsconfig.json` that extends tazuna's:

   ```json
   { "extends": "@natsuzora-dev/tazuna/tsconfig.base.json" }
   ```

   If you already have a `tsconfig.json`, add the `extends` line to it.

## Test a first scenario

In this section, we copy the spec of the ToDo sample, run its scenarios, break one of them, and fix it with the help of `tazuna explain`.
Run the commands in the folder of your `package.json`.

1. Copy the spec that tazuna ships:

   ```sh
   cp -R node_modules/@natsuzora-dev/tazuna/samples/todo/spec spec
   ```

2. Check the spec:

   ```sh
   npx tazuna check spec
   ```

   The output ends with `29 files: no violations`.

3. Open `spec/todo/scenarios.ts`, your copy of the sample's [todo/scenarios.ts](samples/todo/spec/todo/scenarios.ts), and find the scenario `completeTwice`.
   The user adds a task and completes it twice, and the `todo` service rejects the second completion:

   ```ts
   export const completeTwice = scenario({
     description: "Complete a task twice; todo rejects the second completeTask by requires notCompleted",
     given: noTasks,
     when: (w) => {
       addMilk(w, startOf("2026-10-26"));
       w.clock.at(parseInstant("2026-10-25T10:01:00+09:00"));
       const first = w.client.as("screens").send(completeTask, { taskId: "task-1" });
       const second = w.client.as("screens").send(completeTask, { taskId: "task-1" });
       return { first, second };
     },
     then: ({ first, second }) => [
       answered(first, accepted()),
       emitted(first, [eventOf(taskCompleted, { taskId: "task-1", at: parseInstant("2026-10-25T10:01:00+09:00") })]),
       answered(second, rejected("requires", "notCompleted")),
       emitted(second, []),
     ],
   });
   ```

   `given` sets where the scenario starts, `when` lists its lines in order, and `then` states what `todo` did on those lines.
   `noTasks`, `addMilk` and `startOf` are defined earlier in the same file.

4. Run the scenarios:

   ```sh
   npx tazuna test spec
   ```

   The output ends with `67/67 scenarios: no violations`.
   `test` compared the run of each scenario with its snapshot.
   Open `spec/todo/__snapshots__/completeTwice.jsonl` to see one: each line is a message that `todo` received (`"dir":"in"`) or sent (`"dir":"out"`).

5. In Then, change the expected answer of `first` from `accepted()` to `rejected("requires", "notCompleted")`, and run the scenarios again.
   The output is a violation line, followed by `67/67 scenarios: 1 violation`:

   ```json
   {"kind":"InvalidScenario.unmetExpectation","definition":null,"data":{"expectation":0,"expected":[{"result":"rejected","rejection":{"kind":"requires","reason":"notCompleted"}}],"actual":[{"result":"accepted"}]},"location":{"file":"spec/todo/scenarios.ts","line":70},"scenario":{"service":"todo","name":"completeTwice"}}
   ```

6. Ask tazuna what the violation means:

   ```sh
   npx tazuna explain InvalidScenario.unmetExpectation
   ```

   The output says what the violation means and that the scenario is the side at fault.

7. Change the answer back to `accepted()`, and run only the scenario that failed:

   ```sh
   npx tazuna test spec --only todo/completeTwice
   ```

   The output ends with `1/67 scenarios (--only): no violations`.

8. Run every scenario again, as in step 4, to see that the fix broke no other scenario.

## Prove the invariants

In this section, we prove the sample's invariants, remove one, and read the counterexample that `prove` reports.

1. Prove the spec:

   ```sh
   npx tazuna prove spec
   ```

   Each line names a property, such as the invariant `createdBeforeNow` of `Task`, and its verdict.
   The invariants and ensures of `todo` are proved.

2. Open `spec/todo/data.ts`, delete the line of the invariant `createdBeforeNow`, and prove the spec again.
   The invariant `completedAfterCreated` now has a counterexample: a task whose `createdAt` is after the current time, which `completeTask` completes before its creation.

3. No run of `todo` reaches that state, because `todo` creates each task at the current time.
   `prove` checks each command from any records where the invariants hold, so it needs that fact as an invariant.
   Put the line back, and prove the spec again to see that `completedAfterCreated` is proved.

## Lay out a project

The ToDo sample keeps its files in this layout:

```text
spec/<service>/              the spec, its bounds, its scenarios, and the __snapshots__ that test --update writes
inputs/<service>/            the inputs that tazuna generate spec inputs writes
web/.traces/<service>/       the traces that the implementation's tests write, which git ignores
```

The implementation's tests drive it through each snapshot and each input with `drive`, from `@natsuzora-dev/tazuna/verify`, and write a trace of each run.
Then `npx tazuna verify spec web/.traces --coverage` checks the traces and lists the parts of the spec that no trace reached.
See the sample's tests in [web/test](https://github.com/natsuzora-dev/tazuna/tree/main/samples/todo/web/test) in the tazuna repository.

## Next steps

- To learn why a spec is written the way it is, read [Concepts](docs/concepts.md).
- To look up what each command guarantees and who fixes each violation, read [Guarantees](docs/guarantees.md).
- To drive tazuna from a coding agent, give it the skill in [skills/tazuna](skills/tazuna/SKILL.md).
- To browse a spec's definitions and scenario snapshots in a browser, run `npx tazuna view spec`.
- To list the commands and options, run `npx tazuna --help`. Each exported function documents itself in its doc comment.
