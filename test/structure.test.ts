import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { loadSpec, type Spec } from "../src/load/load.ts";
import { type ChartStructure, chartStructure, stateNamed } from "../src/syntax/structure.ts";
import { isDescendant, parallelBetween } from "../src/syntax/tree.ts";
import { serviceRoot } from "./examples.ts";

const subject = (path: string) => loadSpec(join(serviceRoot, path));
const chartOf = (spec: Spec, service: string, name: string): ChartStructure => {
  const chart = chartStructure(spec.structure, service, name);
  assert.ok(chart);
  return chart;
};

const exitOrder = await subject("Chart/Config/exit-transition-entry-order");
const closer = chartOf(exitOrder, "todo", "closer");
const childScreen = await subject("Chart/Request/child-screen");
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
      "left compound p/left parent p",
      "m map p/left/m parent left",
      "c1 atomic p/left/m/c1 parent m",
      "right compound p/right parent p",
      "x atomic p/right/x parent right",
      "q atomic q parent -",
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
    `from ${t.source ?? "root"} at ${t.keys.join(".")}[${t.index}] to ${t.target ?? "-"} guards ${t.guards.join(",") || "-"}${t.reenter === null ? "" : ` reenter ${t.reenter}`}`;
  assert.deepEqual([...homeScreen.on, ...homeScreen.states.flatMap((s) => s.transitions)].map(line), [
    "from open at on.countAll[0] to - guards -",
    "from home at on.openList[0] to listing guards -",
    "from home at on.openHelp[0] to helping guards -",
    "from listing at after.minute.onFired[0] to home guards -",
    "from listing at opens.taskList.onDone[0] to home guards -",
    "from helping at opens.help.onDone[0] to home guards -",
  ]);
  assert.deepEqual(stateNamed(homeScreen, "helping")?.activities, [
    { keyword: "opens", name: "help", definition: { service: "screens", name: "helpPanel" }, modal: false },
  ]);
  const reenter = await subject("Chart/Config/reenter");
  const waiting = (name: string) => stateNamed(chartOf(reenter, "todo", name), "waiting")?.transitions[0];
  assert.equal(waiting("keepsDeadline")?.reenter, false);
  assert.equal(waiting("restartsDeadline")?.reenter, true);
  const reminder = chartOf(await subject("Chart/Select/descendant-transition-wins"), "todo", "reminder");
  assert.deepEqual(stateNamed(reminder, "leftWaiting")?.transitions[0]?.guards, ["isLeft"]);
});

test("A screen has the JSON Schema of each control payload, the controls that each state offers, and the child screens it opens", async () => {
  const taskScreen = chartOf(await subject("Screen/Operable/accepted-operations"), "screens", "taskScreen");
  assert.deepEqual(taskScreen.controls, {
    complete: null,
    remind: {
      type: "object",
      properties: { at: { type: "string", format: "date-time" } },
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

test("Commands and events have the JSON Schema of their input and payload and references to the events they emit and to entities", async () => {
  const spec = await subject("Contract/contracts");
  const byName = (name: string) => spec.structure.definitions.find((d) => d.name === name);
  assert.deepEqual(byName("Task"), {
    kind: "entity",
    service: "todo",
    name: "Task",
    key: "id",
    fields: ["id", "title"],
    unique: [],
    references: [],
  });
  const renamed = byName("taskRenamed");
  assert.ok(renamed?.kind === "event");
  assert.equal(renamed.change, "update");
  assert.deepEqual(renamed.entity, { service: "todo", name: "Task" });
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
