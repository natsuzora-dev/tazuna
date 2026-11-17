# tazuna

tazuna is a language for specifying services in TypeScript.
Lean 4 defines what a spec means, so each spec has exactly one meaning.

A spec defines services: their entities, commands, queries, events, automations, machines, screens, and contracts.
Scenarios state what a service does: Given sets the start, When writes each act in order, and Then states what the service answered, emitted, and requested.
The `tazuna` command checks the spec, simulates the scenarios, and compares an implementation's traces with the simulation.

## Install tazuna

tazuna is published to GitHub Packages.

1. Add the following line to your project's `.npmrc`:

   ```
   @natsuzora-dev:registry=https://npm.pkg.github.com
   ```

2. Authenticate to GitHub Packages with a token that has the `read:packages` scope.
3. Install tazuna and its peers:

   ```sh
   npm install -D @natsuzora-dev/tazuna typescript zod @types/node
   ```

4. Add `"extends": "@natsuzora-dev/tazuna/tsconfig.base.json"` to your `tsconfig.json`.

## Test a first scenario

In this section, we test a scenario of the ToDo sample in [samples/todo](samples/todo): the user completes a task twice, and the `todo` service rejects the second completion.

1. Define the service.
   `service()` returns the definers of one service, `scenario` among them:

   ```ts
   export const { command, query, event, contract, scenario } = service({
   	name: "todo",
   	description: "Keep the user's tasks and remind the user of them",
   	entities: { Task, Settings },
   });
   ```

2. Write the scenario.
   `addTask` and `completeTask` are commands that `samples/todo/spec/todo/commands.ts` defines.
   `peers` lists every service that `todo` exchanges messages with.
   `todo` asks the external service `calendar` for the next business day, so the scenario writes the delivery of that request and of its answer:

   ```ts
   const peers = {
   	calendar: external(calendar),
   	device: external(device),
   	notifier: skip(notifier, "notifier's reactions to todo's events are notifier's scenarios"),
   	screens: skip(screens, "the screens' subscriptions are the screens' scenarios"),
   } as const;

   export const completeTwice = scenario("Complete a task twice; todo rejects the second completeTask", {
   	given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [], Settings: { shouldRemind: true } }, peers },
   	when: (w) => {
   		const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
   		w.net.deliver(add.request(calendar.nextBusinessDay));
   		w.net.deliver(w.peer.calendar.answer(add.request(calendar.nextBusinessDay), { result: "fulfilled", output: { day: "2026-10-26" } }));
   		const first = w.client.send(completeTask, { taskId: "task-1" });
   		const second = w.client.send(completeTask, { taskId: "task-1" });
   		return { first, second };
   	},
   	then: ({ first, second }) => [
   		answered(first, { result: "accepted" }),
   		answered(second, { result: "rejected", rejection: { kind: "requires", reason: "notCompleted" } }),
   	],
   });
   ```

3. Simulate the scenario and write its snapshot:

   ```sh
   npx tazuna test spec --depth 1 --update
   ```

   tazuna writes the trace of the simulation to `spec/todo/__snapshots__/completeTwice.jsonl`.
   Read the snapshot: each line is one message that `todo` received (`"dir":"in"`) or sent (`"dir":"out"`).

4. Run the test again:

   ```sh
   npx tazuna test spec --depth 1
   ```

   The last line of the output is `No violations found.`
   `test` also appends up to one more act to the scenario and reports any violation that the longer run finds.

5. To check an implementation, drive it through each snapshot with `drive` from `@natsuzora-dev/tazuna/verify`, write the traces, and compare them with the snapshots:

   ```sh
   npx tazuna verify spec traces
   ```

   [samples/todo/web](samples/todo/web) is an implementation that does this.

## Next steps

- To write specs and scenarios, see [Write specs](docs/writing-specs.md).
- To learn what `check`, `test`, and `verify` guarantee when they pass, see [Guarantees](docs/guarantees.md).
- To list the commands and their options, run `npx tazuna --help`.
- Facts about one definition, such as `service()` or `Adapter`, are in its doc comment.
