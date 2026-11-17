# tazuna

tazuna is a language for specifying services in TypeScript.
Lean 4 defines what a spec means, so each spec has exactly one meaning.

A spec defines services: their entities, commands, queries, events, automations, machines, screens, and contracts.
Scenarios state what a service does: Given sets the start, When writes each act in order, and Then states what the service answered, emitted, and requested.
The `tazuna` command checks the spec, simulates the scenarios, and compares an implementation's traces with the simulation.
Each meaning has one form, so the author of a spec, often an LLM, has no variant to choose and no step to leave out.

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

In this section, you test a scenario of the ToDo sample in [samples/todo](samples/todo).
The user completes a task twice, and the `todo` service rejects the second completion.
Run the commands in `samples/todo`, whose spec folder is `spec`.

1. Read the service definition.
   `service()` returns the definers of one service, `scenario` among them.
   The following code is shortened from [spec/todo/data.ts](samples/todo/spec/todo/data.ts), which also defines the entities `Task` and `Settings`:

   ```ts
   export const { command, query, event, contract, scenario } = service({
     name: "todo",
     description: "Keep the user's tasks and remind the user of them",
     entities: { Task, Settings },
   });
   ```

2. Read the scenario.
   The following file is a shortened version of the scenario `completeTwice` in [spec/todo/scenarios.ts](samples/todo/spec/todo/scenarios.ts).
   `peers` lists every service that `todo` exchanges messages with.
   `todo` asks the external service `calendar` for the next business day.
   The request and the answer each stay in flight until a `w.net.deliver` line delivers them.

   ```ts
   import { answered, external, skip } from "@natsuzora-dev/tazuna";
   import { calendar } from "../calendar/contract.ts";
   import { device } from "../device/contract.ts";
   import { notifier } from "../notifier/contract.ts";
   import { screens } from "../screens/contract.ts";
   import { addTask, completeTask } from "./commands.ts";
   import { scenario } from "./data.ts";

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
       w.net.deliver(
         w.peer.calendar.answer(add.request(calendar.nextBusinessDay), {
           result: "fulfilled",
           output: { day: "2026-10-26" },
         }),
       );
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

3. Simulate the scenarios and write their snapshots:

   ```sh
   npx tazuna test spec --depth 1 --update
   ```

   tazuna writes the trace of each simulation to the scenario's snapshot, such as `spec/todo/__snapshots__/completeTwice.jsonl`.
   Read the snapshot: each line is one message that `todo` received (`"dir":"in"`) or sent (`"dir":"out"`).

4. Run the test again:

   ```sh
   npx tazuna test spec --depth 1
   ```

   The output ends with `No violations found.`
   `test` also appends up to one [move](docs/guarantees.md#detections) (`--depth 1`) to each scenario and reports any violation that the longer run finds.

5. To check an implementation, drive it through each scenario with `drive` from `@natsuzora-dev/tazuna/verify`, and write each trace to `<traces>/<service>/<scenario>.jsonl`.
   The ToDo sample's server does this in [web/test/todo.test.ts](samples/todo/web/test/todo.test.ts):

   ```ts
   test.for(spec.scenarios.filter((s) => s.service === "todo"))(
     "drive writes the trace of todo's scenario $name",
     async (scenario) => {
       writeTrace("todo", scenario.name, await drive(spec, scenario, serverAdapter("todo")));
     },
   );
   ```

   `spec` comes from `loadSpec` in `@natsuzora-dev/tazuna/load`, `serverAdapter` is the sample's `Adapter` for its server, and `writeTrace` writes the trace to `web/.traces/todo/<scenario>.jsonl`.
   To drive the runs of a running peer, pass each item of `peerSnapshots(spec)` to `drive` in the same way.
   After the sample's tests write the traces, compare them with the snapshots:

   ```sh
   npx tazuna verify spec web/.traces
   ```

## Next steps

- To write specs and scenarios, see [Write specs](docs/writing-specs.md).
- To learn what `check`, `test`, and `verify` guarantee when they pass, see [Guarantees](docs/guarantees.md).
- To list the commands and their options, run `npx tazuna --help`.
- Facts about one definition, such as `service()` or `Adapter`, are in its doc comment.
