import assert from "node:assert/strict";
import { cpSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { loadSpec } from "../src/load/load.ts";
import { viewModel } from "../src/view/model.ts";
import type { StateView, Trigger } from "../src/view/types.ts";

test("The model that viewModel builds from samples/todo/spec holds, for each service, its kind, its description, the services whose contracts it uses, and the number of definitions of each kind", async () => {
  const model = viewModel(await loadSpec(join(import.meta.dirname, "../samples/todo/spec")), "samples/todo/spec");
  assert.deepEqual(
    model.services.map((s) => {
      const counts: Record<string, number> = {};
      for (const d of s.definitions) counts[d.kind] = (counts[d.kind] ?? 0) + 1;
      return { kind: s.kind, name: s.name, description: s.description, uses: s.uses, counts };
    }),
    [
      {
        kind: "external",
        name: "calendar",
        description: "Return the next business day",
        uses: [],
        counts: { query: 1 },
      },
      {
        kind: "external",
        name: "device",
        description: "Show notifications to the user and request permission to show them",
        uses: [],
        counts: { command: 2, event: 2 },
      },
      {
        kind: "service",
        name: "notifier",
        description: "Notify the user about open tasks, with the notification permission that it requests",
        uses: ["device", "todo"],
        counts: { automation: 6, command: 4, entity: 2, event: 4, machine: 2 },
      },
      {
        kind: "screens",
        name: "screens",
        description: "Show the task list and the task details",
        uses: ["todo"],
        counts: { screen: 2 },
      },
      {
        kind: "service",
        name: "todo",
        description: "Keep the user's tasks and remind the user of them",
        uses: ["calendar", "device"],
        counts: { automation: 1, command: 10, entity: 2, event: 16, machine: 2, query: 3 },
      },
    ],
  );
});

test("viewModel turns, in the definition JSON, Zod schemas into JSON Schema, functions into source strings, and other definitions into references by kind, service, and name", async () => {
  const model = viewModel(await loadSpec(join(import.meta.dirname, "../samples/todo/spec")), "samples/todo/spec");
  const addTask = model.services.find((s) => s.name === "todo")?.definitions.find((d) => d.name === "addTask");
  const definition = addTask?.definition as Readonly<Record<string, unknown>>;
  assert.equal(definition["service"], "todo");
  assert.deepEqual(definition["input"], {
    taskId: { type: "string" },
    title: { type: "string", minLength: 1, description: "The name of the task" },
  });
  assert.match(String(definition["decide"]), /^\(\{ input, now \}\) =>/);
  assert.deepEqual(definition["emits"], [
    { kind: "event", service: "todo", name: "taskAddedRecorded" },
    { kind: "event", service: "todo", name: "taskAdded" },
  ]);
});

test("An entity in viewModel has its key, its unique, its invariant names, the type, nullable flag, and description of each field, and the entity that ref() points to", async () => {
  const model = viewModel(await loadSpec(join(import.meta.dirname, "../samples/todo/spec")), "samples/todo/spec");
  const entity = (service: string, name: string) =>
    model.services.find((s) => s.name === service)?.definitions.find((d) => d.name === name)?.entity;
  const fields = (service: string, name: string) =>
    entity(service, name)?.fields.map(
      (f) =>
        `${f.name} ${f.type}${f.nullable ? "?" : ""}${f.ref === null ? "" : ` -> ${f.ref.service}.${f.ref.name}`}${f.description === null ? "" : ` ${f.description}`}`,
    );
  assert.deepEqual(fields("todo", "Task")?.slice(1, 4), [
    "title string The name of the task",
    "createdAt datetime",
    "completedAt datetime?",
  ]);
  assert.deepEqual(fields("todo", "Task")?.at(-1), "reminderDecision enum");
  assert.deepEqual(fields("notifier", "OpenTask"), ["taskId string -> todo.Task"]);
  const { fields: _, ...task } = entity("todo", "Task") ?? {};
  assert.deepEqual(task, {
    key: "id",
    unique: [],
    invariants: ["completedAfterCreated"],
  });
  const { fields: __, ...settings } = entity("todo", "Settings") ?? {};
  assert.deepEqual(settings, {
    key: null,
    unique: [],
    invariants: [],
  });
  assert.equal(entity("todo", "addTask"), null);
});

test("viewModel turns a schema whose default function throws into {}, as the structure that loading builds does, and converts the other fields", async () => {
  const model = viewModel(
    await loadSpec(join(import.meta.dirname, "load/malformed/defaults/conversion")),
    "load/malformed/defaults/conversion",
  );
  const definition = (name: string) =>
    model.services.find((s) => s.name === "todo")?.definitions.find((d) => d.name === name);
  const addNote = definition("addNote")?.definition as Readonly<Record<string, unknown>>;
  assert.deepEqual(addNote["input"], { text: {} });
  assert.deepEqual(
    definition("Task")?.entity?.fields.map((f) => `${f.name} ${f.type}`),
    ["id string", "title any"],
  );
});

function chartLines(state: StateView, depth = 0): string[] {
  const head = [
    state.name,
    state.kind === "atomic" || state.kind === "compound" ? "" : state.kind,
    state.initial === null ? "" : `initial ${state.initial}`,
    ...state.activities.map((r) => `${r.keyword} ${r.kind} ${r.name}`),
  ];
  const trigger = (t: Trigger) => {
    if (t.type === "event" || t.type === "control") return `${t.type} ${t.name}`;
    if (t.type === "after") return `after ${t.deadline}`;
    if (t.type === "answer") return `${t.keyword} ${t.name} ${t.answer}`;
    return t.type;
  };
  return [
    "  ".repeat(depth) + head.filter((part) => part !== "").join(" "),
    ...state.transitions.map(
      (t) =>
        `${"  ".repeat(depth + 1)}${trigger(t.trigger)}${t.guards.map((g) => ` [${g}]`).join("")} -> ${t.target ?? "-"}${t.reenter ? " reenter" : ""} as ${t.id}`,
    ),
    ...state.states.flatMap((child) => chartLines(child, depth + 1)),
  ];
}

test("A chart in viewModel has the state tree of its machine or screen, and the activities and transitions of each state with the trigger kind, guard names, and id of each transition", async () => {
  const model = viewModel(await loadSpec(join(import.meta.dirname, "../samples/todo/spec")), "samples/todo/spec");
  const chart = (name: string) => {
    const state = model.services.flatMap((s) => s.definitions).find((d) => d.name === name)?.chart;
    assert.ok(state);
    return chartLines(state);
  };
  assert.deepEqual(chart("taskDetailScreen"), [
    "taskDetailScreen initial editing",
    "  control close -> closed as on.close[0] in root",
    "  event taskDeleted [thisTask] -> closed as on.taskDeleted[0] in root",
    "  editing parallel shows query taskDetail",
    "    control delete -> deleting as on.delete[0] in editing",
    "    title initial viewing",
    "      viewing",
    "        control rename [changed] -> renaming as on.rename[0] in viewing",
    "      renaming sends command renameTask",
    "        sends renameTask onAccepted -> viewing as sends.renameTask.onAccepted[0] in renaming",
    "        sends renameTask onRejected -> viewing as sends.renameTask.onRejected[0] in renaming",
    "    completion initial ready",
    "      ready",
    "        control complete -> completing as on.complete[0] in ready",
    "        control reopen -> reopening as on.reopen[0] in ready",
    "      completing sends command completeTask",
    "        sends completeTask onAccepted -> ready as sends.completeTask.onAccepted[0] in completing",
    "        sends completeTask onRejected -> ready as sends.completeTask.onRejected[0] in completing",
    "      reopening sends command reopenTask",
    "        sends reopenTask onAccepted -> ready as sends.reopenTask.onAccepted[0] in reopening",
    "        sends reopenTask onRejected -> ready as sends.reopenTask.onRejected[0] in reopening",
    "    due initial collapsed",
    "      collapsed",
    "        control dueToggle -> expanded as on.dueToggle[0] in collapsed",
    "      expanded",
    "        control dueToggle -> collapsed as on.dueToggle[0] in expanded",
    "        control dueChoose [unchanged] -> collapsed as on.dueChoose[0] in expanded",
    "        control dueChoose [selectable] -> changing as on.dueChoose[1] in expanded",
    "        control dueClear -> changing as on.dueClear[0] in expanded",
    "      changing sends command changeDue",
    "        sends changeDue onAccepted -> collapsed as sends.changeDue.onAccepted[0] in changing",
    "        sends changeDue onRejected -> collapsed as sends.changeDue.onRejected[0] in changing",
    "  deleting sends command deleteTask",
    "    sends deleteTask onAccepted -> closed as sends.deleteTask.onAccepted[0] in deleting",
    "    sends deleteTask onRejected -> editing as sends.deleteTask.onRejected[0] in deleting",
    "  closed final",
  ]);
  assert.deepEqual(chart("taskListScreen").slice(0, 4), [
    "taskListScreen initial showing",
    "  showing initial listing shows query reminderSettings shows query tasks",
    "    control filter -> - as on.filter[0] in showing",
    "    listing",
  ]);
  assert.ok(chart("taskListScreen").includes("    detail opens screen taskDetail"));
  assert.ok(
    chart("taskListScreen").includes(
      "      opens taskDetail onDone -> listing as opens.taskDetail.onDone[0] in detail",
    ),
  );
  assert.deepEqual(chart("workload").slice(-3), [
    "  warned",
    "    event openTaskRecorded -> warned reenter as on.openTaskRecorded[0] in warned",
    "    after periodEnd -> quiet as after.periodEnd.onFired[0] in warned",
  ]);
  assert.ok(chart("workload").includes("    always [tooMany] -> warning as always[0] in quiet"));
  assert.ok(
    chart("reminder").includes("      after reminderTime -> recording as after.reminderTime.onFired[0] in waiting"),
  );
});

test("A scenario in viewModel has, for each snapshot line, the sender and receiver lifelines of the sequence diagram", async () => {
  const model = viewModel(await loadSpec(join(import.meta.dirname, "../samples/todo/spec")), "samples/todo/spec");
  const flow = (service: string, name: string) => {
    const scenario = model.scenarios.find((s) => s.service === service && s.name === name);
    assert.ok(scenario?.trace);
    const trace = scenario.trace;
    return [
      scenario.lifelines.join(" "),
      ...scenario.entries.map((entry) => {
        const l = trace[entry.line];
        const place = l === undefined ? "" : "name" in l ? l.name : "to" in l ? l.to : "";
        const head = `${entry.line} ${l?.dir} ${l?.type} ${place}`;
        if (entry.type === "time") return head;
        const side = (p: string | null) => p ?? "scenario";
        return `${head}: ${side(entry.from)} -> ${side(entry.to)}`;
      }),
    ];
  };
  assert.deepEqual(flow("todo", "remindAddedWhileAsking").slice(0, 10), [
    "todo calendar",
    "0 in command addTask: scenario -> todo",
    "1 out answer addTask#1: todo -> scenario",
    "2 out event taskAddedRecorded: todo -> todo",
    "3 out event taskAdded: todo -> todo",
    "4 out query calendar.nextBusinessDay: todo -> calendar",
    "5 in command addTask: scenario -> todo",
    "6 out answer addTask#2: todo -> scenario",
    "7 out event taskAddedRecorded: todo -> todo",
    "8 out event taskAdded: todo -> todo",
  ]);
  assert.deepEqual(flow("screens", "closesDeletedTask"), [
    "screens todo",
    "0 out subscribe todo.reminderSettings: screens -> todo",
    "1 out subscribe todo.tasks: screens -> todo",
    "2 in answer todo.tasks#1: todo -> screens",
    "3 in answer todo.reminderSettings#1: todo -> screens",
    "4 in operation taskListScreen.openTask: scenario -> screens",
    "5 out subscribe todo.taskDetail: screens -> todo",
    "6 in event todo.taskDeleted: todo -> screens",
    "7 out unsubscribe todo.taskDetail#1: screens -> todo",
  ]);
  assert.deepEqual(flow("todo", "answersSubscriptions").slice(-3), [
    "16 out answer taskDetail#1: todo -> scenario",
    "17 in unsubscribe tasks#1: scenario -> todo",
    "18 in unsubscribe taskDetail#1: scenario -> todo",
  ]);
  assert.ok(flow("todo", "remindAtRemindAt").includes("7 in time "));
});

test("For a scenario whose snapshot has a line outside the trace line schema, viewModel holds the line number and reason instead of the trace, and reads the traces of the other scenarios", async () => {
  mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
  const copy = mkdtempSync(join(import.meta.dirname, ".fixtures", "view-"));
  try {
    cpSync(join(import.meta.dirname, "../samples/todo/spec"), copy, { recursive: true });
    writeFileSync(join(copy, "todo/__snapshots__/completeTwice.jsonl"), '{"time":"2026-10-25T01:00:00Z"}\nnot json\n');
    const model = viewModel(await loadSpec(copy), copy);
    const scenario = (name: string) => model.scenarios.find((s) => s.service === "todo" && s.name === name);
    assert.deepEqual(
      { trace: scenario("completeTwice")?.trace, error: scenario("completeTwice")?.error },
      {
        trace: null,
        error: {
          lineNumber: 1,
          issues: [
            {
              code: "invalid_union",
              errors: [],
              note: "No matching discriminator",
              discriminator: "type",
              options: [
                "command",
                "query",
                "subscribe",
                "answer",
                "unsubscribe",
                "event",
                "operation",
                "time",
                "restart",
              ],
              path: ["type"],
              message:
                "Invalid discriminator value. Expected 'command' | 'query' | 'subscribe' | 'answer' | 'unsubscribe' | 'event' | 'operation' | 'time' | 'restart'",
            },
          ],
        },
      },
    );
    assert.equal(scenario("remindAtDue")?.error, null);
    assert.notEqual(scenario("remindAtDue")?.trace, null);
  } finally {
    rmSync(copy, { recursive: true, force: true });
  }
});
