import assert from "node:assert/strict";
import { test } from "node:test";
import { calendar } from "../samples/todo/spec/calendar/contract.ts";
import { device } from "../samples/todo/spec/device/contract.ts";
import { scenario } from "../samples/todo/spec/screens/data.ts";
import { taskListScreen } from "../samples/todo/spec/screens/taskListScreen.ts";
import { todo } from "../samples/todo/spec/todo/contract.ts";
import type { DefinitionRef } from "../src/data/definitionRef.ts";
import { created, external, raw, requested, requestOf, run } from "../src/index.ts";
import type { ScenarioDefinition, When } from "../src/scenario/define.ts";
import { lower } from "../src/scenario/lower.ts";

const refs = new Map<unknown, DefinitionRef>([
  ...Object.entries(todo).map(([name, d]) => [d, { service: "todo", name }] as const),
  ...Object.entries(calendar).map(([name, d]) => [d, { service: "calendar", name }] as const),
  ...Object.entries(device).map(([name, d]) => [d, { service: "device", name }] as const),
  [taskListScreen, { service: "screens", name: "taskListScreen" }],
]);
const services = new Map<unknown, string>([
  [todo, "todo"],
  [calendar, "calendar"],
]);

const peers = [run(todo, { Task: [], Settings: { shouldRemind: true } }), external(calendar), external(device)];

function lowered(when: (w: When<typeof peers>) => unknown, then: (lines: never) => readonly never[] = () => []) {
  const definition = scenario({
    description: "lowered",
    given: { start: 1_792_890_000_000, records: {}, peers },
    when,
    then: then as never,
  }) as ScenarioDefinition;
  const { lines, expectations, violations } = lower(
    definition,
    (d) => refs.get(d),
    (c) => services.get(c),
  );
  return { lines, expectations, violations };
}

const startup = { type: "startup" } as const;
const line = (index: number) => ({ type: "line", index }) as const;

test("A handle's observed value in a written value becomes a hole that reads the handle's fact", () => {
  const { lines } = lowered((w) => {
    const adding = w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.call(todo.taskDetail, { taskId: adding.request(calendar.nextBusinessDay).input.after as never });
  });
  assert.deepEqual(lines[1], {
    type: "request",
    kind: "query",
    target: { service: "todo", name: "taskDetail" },
    input: {
      value: { taskId: null },
      holes: [
        {
          path: ["taskId"],
          fill: {
            type: "ref",
            value: {
              fact: {
                type: "request",
                origin: line(0),
                kind: "query",
                target: { service: "calendar", name: "nextBusinessDay" },
              },
              part: "input",
              path: ["after"],
            },
          },
        },
      ],
    },
  });
});

test("A pick that holds an observed value becomes a template, and a subscription handle names a subscribe request", () => {
  const { lines } = lowered((w) => {
    const watching = w.startup.subscription(todo.tasks, { filter: "open" });
    const adding = w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
    w.net.deliver(adding.request(todo.completeTask, { taskId: watching.input.filter }));
  });
  assert.deepEqual(lines[1], {
    type: "deliver",
    message: {
      type: "request",
      origin: line(0),
      kind: "command",
      target: { service: "todo", name: "completeTask" },
      input: {
        value: { taskId: null },
        holes: [
          {
            path: ["taskId"],
            fill: {
              type: "ref",
              value: {
                fact: {
                  type: "request",
                  origin: startup,
                  kind: "subscribe",
                  target: { service: "todo", name: "tasks" },
                  input: { value: { filter: "open" }, holes: [] },
                },
                part: "input",
                path: ["filter"],
              },
            },
          },
        ],
      },
    },
  });
});

test("created() becomes a created hole, and raw() writes its value as is", () => {
  const { lines } = lowered((w) => {
    w.peer.todo.send(todo.completeTask, { taskId: created() });
    w.client.send(todo.addTask, raw({ taskId: "task-1", title: 7 }));
  });
  assert.deepEqual(
    lines.map((l) => (l.type === "request" ? l.input : undefined)),
    [
      { value: { taskId: null }, holes: [{ path: ["taskId"], fill: { type: "created" } }] },
      { value: { taskId: "task-1", title: 7 }, holes: [] },
    ],
  );
});

test("A peer's line names the message it states; a deliver line names it too, and names what its processing caused", () => {
  const { lines } = lowered((w) => {
    const sent = w.peer.calendar.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
    const reached = w.net.deliver(sent);
    w.net.leaveInFlight(reached.answer(sent));
    const told = w.peer.device.emit(device.notificationPermissionGranted, {}, { resultOf: null });
    w.net.deliver(told.to(todo));
    const watching = w.startup.subscription(todo.tasks);
    w.net.lose(reached.end(watching));
  });
  assert.deepEqual(lines.slice(1), [
    { type: "deliver", message: line(0) },
    { type: "leaveInFlight", message: { type: "answer", origin: line(1), to: 0 } },
    {
      type: "emit",
      peer: "device",
      event: { service: "device", name: "notificationPermissionGranted" },
      payload: { value: {}, holes: [] },
    },
    {
      type: "deliver",
      message: {
        type: "event",
        origin: line(3),
        event: { service: "device", name: "notificationPermissionGranted" },
        receiver: "todo",
      },
    },
    {
      type: "lose",
      message: {
        type: "end",
        origin: line(1),
        subscription: {
          type: "request",
          origin: startup,
          kind: "subscribe",
          target: { service: "todo", name: "tasks" },
        },
      },
    },
  ]);
});

test("Then lowers each expectation about the line it names", () => {
  const { expectations } = lowered(
    (w) => ({ adding: w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" }) }),
    (({ adding }: { adding: never }) => [
      requested(adding, [requestOf(calendar.nextBusinessDay, { after: 1_792_890_000_000 })]),
    ]) as never,
  );
  assert.deepEqual(expectations, [
    {
      type: "requested",
      line: 0,
      requests: [
        {
          kind: "query",
          target: { service: "calendar", name: "nextBusinessDay" },
          input: { value: { after: 1_792_890_000_000 }, holes: [] },
        },
      ],
      ends: [],
    },
  ]);
});

for (const [use, misuse] of [
  ["spread", (o: Record<string, unknown>) => ({ ...o })],
  ["conversion", (o: Record<string, unknown>) => `${o["task"] as string}`],
  ["unknownField", (o: Record<string, unknown>) => (o["task"] as { map: unknown }).map],
  ["presence", (o: Record<string, unknown>) => "task" in o],
] as const)
  test(`An observed value used as ${use} is a violation of the line that uses it, not an error`, () => {
    const { violations } = lowered((w) => {
      const asking = w.client.call(todo.taskDetail, { taskId: "task-1" });
      w.client.send(todo.addTask, { taskId: "task-2", title: misuse(asking.output as never) as never });
    });
    assert.equal(violations.length, 1);
    assert.equal(violations[0]?.kind, "misusedObserved");
    assert.equal(violations[0]?.kind === "misusedObserved" ? violations[0].use : undefined, use);
  });

test("A pick is the content itself, and an event's route comes after it", () => {
  const { lines } = lowered((w) => {
    const adding = w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
    w.net.deliver(adding.request(calendar.nextBusinessDay, { after: 1_792_886_400_000 }));
    w.net.deliver(adding.event(todo.taskAdded, { taskId: "task-1" }, { to: todo }));
  });
  assert.deepEqual(lines.slice(1), [
    {
      type: "deliver",
      message: {
        type: "request",
        origin: line(0),
        kind: "query",
        target: { service: "calendar", name: "nextBusinessDay" },
        input: { value: { after: 1_792_886_400_000 }, holes: [] },
      },
    },
    {
      type: "deliver",
      message: {
        type: "event",
        origin: line(0),
        event: { service: "todo", name: "taskAdded" },
        payload: { value: { taskId: "task-1" }, holes: [] },
        receiver: "todo",
      },
    },
  ]);
});

test("A position read in a bag of an observed value is a violation, and one in a sequence is a hole", () => {
  const { violations } = lowered((w) => {
    const listed = w.client.call(todo.tasks, { filter: "all" });
    w.client.send(todo.completeTask, {
      taskId: (listed.output.tasks as never as { taskId: string }[])[0]?.taskId as never,
    });
  });
  assert.deepEqual(
    violations.map((p) => (p.kind === "misusedObserved" ? [p.use, p.path] : p.kind)),
    [["position", ["tasks"]]],
  );
});

test("A line placed after When returned, and a definition the spec does not name, are violations", () => {
  const after = lowered((w) => ({ w }), (({ w }: { w: When<typeof peers> }) => {
    w.host.restart();
    return [];
  }) as never);
  assert.deepEqual(after.violations, [{ kind: "lineAfterWhen" }]);
  const unnamed = lowered((w) => w.client.send({ kind: "command" } as never, {} as never));
  assert.deepEqual(unnamed.violations, [{ kind: "unnamed", path: ["lines", 0] }]);
});
