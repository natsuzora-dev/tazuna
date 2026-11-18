# tazuna

tazuna is a language for specifying services in TypeScript.
Lean 4 defines what a spec means, so each spec has exactly one meaning.

A spec defines services, and scenarios state what a service does.
The `tazuna` command checks the spec, simulates the scenarios, and compares an implementation's traces with the simulation.

## Install tazuna

tazuna is published to GitHub Packages.

1. Add the following line to your project's `.npmrc`:

   ```
   @natsuzora-dev:registry=https://npm.pkg.github.com
   ```

2. Authenticate to GitHub Packages with a token that has the `read:packages` scope.
3. Install tazuna, its peers `typescript` and `zod`, and `@types/node`:

   ```sh
   npm install -D @natsuzora-dev/tazuna typescript zod @types/node
   ```

4. Add `"extends": "@natsuzora-dev/tazuna/tsconfig.base.json"` to your `tsconfig.json`.

## Test a first scenario

In this section, we check the spec of the ToDo sample, simulate one of its scenarios, and see where an implementation comes in.
Run the commands in [samples/todo](samples/todo).

1. Open [spec/todo/scenarios.ts](samples/todo/spec/todo/scenarios.ts) and find the scenario `completeTwice`.
   The user adds a task and completes it twice, and the `todo` service rejects the second completion:

   ```ts
   export const completeTwice = scenario(
     "Complete a task twice; todo rejects the second completeTask by requires notCompleted",
     {
       given: noTasks,
       when: (w) => {
         addMilk(w, "2026-10-26");
         w.clock.at("2026-10-25T10:01:00+09:00");
         const first = w.client.send(completeTask, { taskId: "task-1" });
         const second = w.client.send(completeTask, { taskId: "task-1" });
         return { first, second };
       },
       then: ({ first, second }) => [
         answered(first, accepted),
         emitted(first, [event(taskCompleted, { taskId: "task-1" })]),
         answered(second, requires("notCompleted")),
         emitted(second, []),
       ],
     },
   );
   ```

   Given is the start, When is the lines in order, and Then is what `todo` did on those lines.
   `noTasks`, `accepted`, `requires`, and `addMilk` are plain constants and functions earlier in the same file.
   `addMilk` adds a task and delivers its request to the `calendar` service and the answer.

2. Check the spec:

   ```sh
   npx tazuna check spec
   ```

   The output ends with `No violations found.`

3. Simulate the scenarios and write their snapshots:

   ```sh
   npx tazuna test spec --depth 1 --update
   ```

   tazuna writes the trace of each run to the scenario's snapshot.
   Open `spec/todo/__snapshots__/completeTwice.jsonl`.
   Each line is one message that `todo` received (`"dir":"in"`) or sent (`"dir":"out"`).
   The last two lines are the second `completeTask` request and its rejection.

4. In Then, change the expected answer of `first` from `accepted` to `requires("notCompleted")`, and run the test again:

   ```sh
   npx tazuna test spec --depth 1
   ```

   The output is a JSON line whose `kind` is `InvalidScenario.unmetExpectation`.
   Change the answer back to `accepted`, and run the test again.
   The output ends with `No violations found.`

5. To compare an implementation with the snapshots, an implementation test first checks the spec with `checkSpec` from `@natsuzora-dev/tazuna/verify`.
   It then drives the implementation through each scenario with `drive` and writes each trace.
   The ToDo sample's server does this in [web/test/todo.test.ts](samples/todo/web/test/todo.test.ts), with the spec from [web/test/support/spec.ts](samples/todo/web/test/support/spec.ts) and the `Adapter` in [web/test/support/serverAdapter.ts](samples/todo/web/test/support/serverAdapter.ts).
   After that test writes the traces to `web/.traces`, compare them:

   ```sh
   npx tazuna verify spec web/.traces
   ```

## Next steps

- To learn the ideas behind specs and scenarios, see [Concepts](docs/concepts.md).
- To learn what `check`, `test`, and `verify` guarantee when they pass, see [Guarantees](docs/guarantees.md).
- To list the commands and their options, run `npx tazuna --help`.
- Each exported function, such as `service()`, `scenario`, or `drive`, documents itself in its doc comment.
