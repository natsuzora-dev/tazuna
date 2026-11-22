import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import type { Spec } from "../src/load/load.ts";
import { type ChartStructure, chartStructure, stateNamed } from "../src/spec/structure.ts";
import { isDescendant, parallelBetween } from "../src/spec/tree.ts";
import { loadedSpec, serviceRoot } from "./examples.ts";

const subject = async (path: string) => await loadedSpec(join(serviceRoot, path));
const chartOf = (spec: Spec, service: string, name: string): ChartStructure => {
  const chart = chartStructure(spec.structure, service, name);
  assert.ok(chart);
  return chart;
};

const exitOrder = await subject("Chart/Config/microstep_exits_in_exit_order");
const closer = chartOf(exitOrder, "todo", "closer");
const childScreen = await subject("Chart/Request/entering_opens_one_child");
const homeScreen = chartOf(childScreen, "screens", "homeScreen");

test("The structure that loadSpec builds stays the same after a JSON round trip", () => {
  for (const spec of [exitOrder, childScreen])
    assert.deepEqual(JSON.parse(JSON.stringify(spec.structure)), spec.structure);
});

test("States come in source order, each with its path of names from the children of root, its parent, and its kind", async () => {
  assert.deepEqual(
    closer.states.map((s) => `${s.name} ${s.kind} ${s.path.join("/")} parent ${s.parent ?? "-"}`),
    [
      "p parallel p parent -",
      "left plain p/left parent p",
      "m map p/left/m parent left",
      "c1 plain p/left/m/c1 parent m",
      "right plain p/right parent p",
      "x plain p/right/x parent right",
      "q plain q parent -",
      "done final done parent -",
    ],
  );
  assert.deepEqual(stateNamed(closer, "left")?.children, ["m"]);
  assert.equal(stateNamed(closer, "m")?.initial, "c1");
  assert.ok(isDescendant(closer, "c1", "p"));
  assert.ok(!isDescendant(closer, "done", "p"));
  const song = chartOf(await subject("Chart/Config/history"), "player", "song");
  assert.equal(stateNamed(song, "resumed")?.kind, "history");
});

test("parallelBetween returns the parallel state that holds the two states in different regions", () => {
  assert.equal(parallelBetween(closer, "c1", "x"), "p");
  assert.equal(parallelBetween(closer, "c1", "m"), null);
  assert.equal(parallelBetween(closer, "left", "c1"), null);
});

test("A transition has the state it is written in, the key and index in its transition array, its target, and its guard names, and a state has its activities", async () => {
  const line = (t: ChartStructure["on"][number]) =>
    `from ${t.source ?? "root"} at ${JSON.stringify(t.trigger)}[${t.index}] to ${t.target ?? "-"} guards ${t.guards.join(",") || "-"}${t.reenter === null ? "" : ` reenter ${t.reenter}`}`;
  assert.deepEqual([...homeScreen.on, ...homeScreen.states.flatMap((s) => s.transitions)].map(line), [
    'from open at {"type":"on","key":"countAll"}[0] to - guards -',
    'from home at {"type":"on","key":"openList"}[0] to listing guards -',
    'from home at {"type":"on","key":"openHelp"}[0] to helping guards -',
    'from listing at {"type":"after","deadline":"minute"}[0] to home guards -',
    'from listing at {"type":"opens","key":"taskList"}[0] to home guards -',
    'from helping at {"type":"opens","key":"help"}[0] to home guards -',
  ]);
  assert.deepEqual(stateNamed(homeScreen, "helping")?.activities, [
    { keyword: "opens", name: "help", definition: { service: "screens", name: "helpPanel" }, modal: false },
  ]);
  const reenter = await subject("Chart/Config/reenter_true_exits");
  const waiting = (name: string) => stateNamed(chartOf(reenter, "todo", name), "waiting")?.transitions[0];
  assert.equal(waiting("keepsDeadline")?.reenter, false);
  assert.equal(waiting("restartsDeadline")?.reenter, true);
  const reminder = chartOf(await subject("Chart/Select/leaf_selects_innermost"), "todo", "reminder");
  assert.deepEqual(stateNamed(reminder, "leftWaiting")?.transitions[0]?.guards, ["isLeft"]);
});

test("A screen has the JSON Schema of each control payload, the controls that each state offers, and the child screens it opens", async () => {
  const taskScreen = chartOf(await subject("Screen/Operable/accepted-operations"), "screens", "taskScreen");
  assert.deepEqual(taskScreen.controls, {
    complete: null,
    remind: {
      type: "object",
      properties: {
        at: {
          type: "integer",
          minimum: -9007199254740991,
          maximum: 9007199254740991,
          "x-tazuna-checks": [{ check: "number_format", format: "safeint", abort: false }],
        },
      },
      required: ["at"],
    },
  });
  assert.deepEqual(taskScreen.offers, { complete: "listed", remind: "listed" });
  assert.deepEqual(
    taskScreen.states.flatMap((s) => Object.entries(s.offers).map(([control, o]) => `${s.name} ${control} ${o}`)),
    ["completed complete listed"],
  );
  assert.deepEqual(homeScreen.screens, {
    taskList: { service: "screens", name: "taskListScreen" },
    help: { service: "screens", name: "helpPanel" },
  });
});

test("Entities, commands and events have the JSON Schema of their fields, input and payload, with the entity of each key, and references to the events they emit and to entities", async () => {
  const spec = await subject("Contract/contracts");
  const byName = (name: string) => spec.structure.definitions.find((d) => d.name === name);
  assert.deepEqual(byName("Task"), {
    kind: "entity",
    service: "todo",
    name: "Task",
    key: "id",
    fields: {
      type: "object",
      properties: { id: { type: "string", "x-tazuna-key": "todo/Task" }, title: { type: "string" } },
      required: ["id", "title"],
    },
    unique: [],
    references: [],
    keys: [{ path: ["id"], entity: { service: "todo", name: "Task" } }],
  });
  const renamed = byName("taskRenamed");
  assert.ok(renamed?.kind === "event");
  assert.deepEqual(renamed.change, { kind: "update", entity: { service: "todo", name: "Task" } });
  assert.deepEqual(Object.keys((renamed.payload as { properties: object }).properties), ["id", "title"]);
  const rename = byName("renameTask");
  assert.ok(rename?.kind === "command");
  assert.deepEqual(
    {
      rejects: rename.rejects,
      emits: rename.emits,
      binds: rename.binds,
      references: rename.references,
      input: (rename.input as { required: unknown }).required,
    },
    {
      rejects: null,
      emits: [{ service: "todo", name: "taskRenamed" }],
      binds: ["task"],
      references: [{ field: "taskId", entity: { service: "todo", name: "Task" } }],
      input: ["taskId", "title"],
    },
  );
});
