# tazuna

tazuna is a language for specifying services in TypeScript.
A spec defines services, and its scenarios state what each service does.
Lean 4 defines what a spec means, and the `tazuna` command checks a spec, simulates its scenarios, and compares an implementation's traces with the simulation.

Before 1.0, a minor version may break the DSL.
Read the docs and samples of the version you installed, in `node_modules/@natsuzora-dev/tazuna`, not those on GitHub.

## Install tazuna

1. Install tazuna, its peers `typescript` and `zod`, and `@types/node`:

   ```sh
   npm install -D @natsuzora-dev/tazuna typescript zod @types/node
   ```

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

   The output ends with `27 files: no violations`.

3. Open `spec/todo/scenarios.ts`, your copy of the sample's [todo/scenarios.ts](samples/todo/spec/todo/scenarios.ts), and find the scenario `completeTwice`.
   The user adds a task and completes it twice, and the `todo` service rejects the second completion:

   ```ts
   export const completeTwice = scenario({
     description: "Complete a task twice; todo rejects the second completeTask by requires notCompleted",
     given: noTasks,
     when: (w) => {
       addMilk(w, "2026-10-26");
       w.clock.at("2026-10-25T10:01:00+09:00");
       const first = w.client.send(completeTask, { taskId: "task-1" });
       const second = w.client.send(completeTask, { taskId: "task-1" });
       return { first, second };
     },
     then: ({ first, second }) => [
       answered(first, accepted()),
       emitted(first, [eventOf(taskCompleted, { taskId: "task-1" })]),
       answered(second, rejected("requires", "notCompleted")),
       emitted(second, []),
     ],
   });
   ```

   `given` sets where the scenario starts, `when` lists its lines in order, and `then` states what `todo` did on those lines.
   `noTasks` and `addMilk` are defined earlier in the same file.

4. Run the scenarios:

   ```sh
   npx tazuna test spec
   ```

   The output ends with `65/65 scenarios, depth 1: no violations`.
   `test` compared the run of each scenario with its snapshot.
   Open `spec/todo/__snapshots__/completeTwice.jsonl` to see one: each line is a message that `todo` received (`"dir":"in"`) or sent (`"dir":"out"`).

5. In Then, change the expected answer of `first` from `accepted()` to `rejected("requires", "notCompleted")`, and run the scenarios again.
   The output is a violation line, followed by `65/65 scenarios, depth 1: 1 violation`:

   ```json
   {"kind":"InvalidScenario.unmetExpectation","definition":null,"data":{"expectation":0,"expected":[{"result":"rejected","rejection":{"kind":"requires","reason":"notCompleted"}}],"actual":[{"result":"accepted"}]},"location":{"file":"spec/todo/scenarios.ts","line":64},"scenario":{"service":"todo","name":"completeTwice"}}
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

   The output ends with `1/65 scenarios (--only), depth 1: no violations`.

8. Run every scenario again, as in step 4, to see that the fix broke no other scenario.

## Next steps

- To learn why a spec is written the way it is, read [Concepts](docs/concepts.md).
- To look up what a passing command guarantees and who fixes each violation, read [Guarantees](docs/guarantees.md).
- To drive tazuna from a coding agent, give it the skill in [skills/tazuna](skills/tazuna/SKILL.md).
- To compare an implementation with the snapshots, see how the ToDo sample's server drives itself through the scenarios in [web/test/todo.test.ts](https://github.com/natsuzora-dev/tazuna/blob/main/samples/todo/web/test/todo.test.ts) in the tazuna repository.
- To browse a spec's definitions and scenario snapshots in a browser, run `npx tazuna view spec`.
- To list the commands and options, run `npx tazuna --help`. Each exported function documents itself in its doc comment.
