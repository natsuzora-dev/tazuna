import { z } from "zod";
import { calendar as calendarPeer } from "../samples/todo/spec/calendar/contract.ts";
import { contract as externalContract, query as externalQuery } from "../samples/todo/spec/calendar/data.ts";
import { device as devicePeer } from "../samples/todo/spec/device/contract.ts";
import { command as externalCommand } from "../samples/todo/spec/device/data.ts";
import { screens as screensPeer } from "../samples/todo/spec/screens/contract.ts";
import { given as givenOfScreens, scenario as scenarioOfScreens } from "../samples/todo/spec/screens/data.ts";
import { taskDetailScreen } from "../samples/todo/spec/screens/taskDetailScreen.ts";
import { taskListScreen } from "../samples/todo/spec/screens/taskListScreen.ts";
import { addTask, completeTask, setReminder } from "../samples/todo/spec/todo/commands.ts";
import { todo as todoPeer } from "../samples/todo/spec/todo/contract.ts";
import {
  automation,
  command,
  query,
  Settings,
  scenario as scenarioOfTodo,
  Task,
} from "../samples/todo/spec/todo/data.ts";
import {
  dueChanged,
  taskAdded,
  taskAddedRecorded,
  taskCompletedRecorded,
  taskDeleted,
  taskDeletedRecorded,
} from "../samples/todo/spec/todo/events.ts";
import { tasks } from "../samples/todo/spec/todo/queries.ts";
import {
  type AnswerOf,
  accepted,
  answered,
  any,
  type Bag,
  bag,
  constants,
  created,
  date,
  emit,
  emitted,
  endOf,
  entity,
  eventOf,
  external,
  externalService,
  fulfilled,
  type InputOf,
  instant,
  type KindOf,
  none,
  type OutputOf,
  parseInstant,
  type RecordsOf,
  type RequestLine,
  type RowOf,
  raw,
  ref,
  rejected,
  requested,
  requestOf,
  run,
  service,
  set,
  singleEntity,
  skip,
  sortedBy,
} from "../src/index.ts";

const { machine, screen, createEvent, updateEvent, deleteEvent, contract } = service({
  name: "test",
  description: "",
  entities: { Task, Settings },
});
const Note = entity({ description: "", fields: { id: z.string() }, key: "id" });
const reminderSettings = externalQuery({ callers: [], output: { enabled: z.boolean() }, rejects: [] });

// @ts-expect-error an update event writes only non-key fields
updateEvent({ entity: Task, writes: ["id"] });

// An update event can update a single entity.
updateEvent({ entity: Settings, writes: ["shouldRemind"] });

// @ts-expect-error key names a field
entity({ description: "", fields: { id: z.string() }, key: "name" });

// ref.self() holds the entity's own key type, in its invariants and in the rows that it reads.
const Reply = entity({
  description: "",
  fields: {
    id: z.string(),
    replyTo: ref.self().nullable(),
    quotes: z.array(ref.self()),
    thread: z.object({ root: ref.self() }),
  },
  key: "id",
  invariants: { notToItself: ({ record }) => record.replyTo !== record.id },
});
const replyTo: string | null = null as unknown as RowOf<typeof Reply>["replyTo"];
const quotes: readonly string[] = [] as unknown as RowOf<typeof Reply>["quotes"];
const root: string = "" as unknown as RowOf<typeof Reply>["thread"]["root"];
// @ts-expect-error a ref.self() value has the key's type
const notKey: RowOf<typeof Reply>["replyTo"] = 1;
// @ts-expect-error a ref.self() value in an object has the key's type
const notNestedKey: RowOf<typeof Reply>["thread"]["root"] = 1;
void [replyTo, quotes, root, notKey, notNestedKey];

// @ts-expect-error a single entity's fields have defaults
singleEntity({ description: "", fields: { remindersEnabled: z.boolean() } });

// @ts-expect-error a create event takes a non-single entity
createEvent({ entity: Settings });

// @ts-expect-error a delete event takes a non-single entity
deleteEvent({ entity: Settings });

// @ts-expect-error an event's entity belongs to the emitting service's entities
createEvent({ entity: Note });

const now = Date.UTC(2026, 9, 25);
// @ts-expect-error an update event's payload has every field in writes
emit(dueChanged, { id: "task-1" });
const tomorrow = now + 86_400_000;
emit(dueChanged, { id: "task-1", dueAt: tomorrow, remindAt: tomorrow, reminderDecision: "decided" });

// @ts-expect-error a payload holds an instant as milliseconds
emit(dueChanged, { id: "task-1", dueAt: "2026-10-25T10:00:00+09:00", remindAt: null, reminderDecision: "pending" });

command({ callers: ["client"], emits: [taskCompletedRecorded] }).decide(() => [
  // @ts-expect-error decide returns only events in emits
  emit(taskDeletedRecorded, { id: "task-1" }),
]);

command({ callers: ["client"], input: { taskIds: z.array(ref(Task)) }, emits: [taskDeletedRecorded] }).decide(
  ({ input, records }) => {
    const task = records.Task.filter((t) => input.taskIds.includes(t.id)).only();
    // @ts-expect-error expressions cannot mutate records
    if (task !== undefined) task.title = "";
    // @ts-expect-error expressions cannot mutate input arrays
    input.taskIds.push("task-2");
    return [];
  },
);

// A function extracted from an expression takes records as RowOf.
const isOpen = (task: RowOf<typeof Task>) => task.completedAt === null;
const shouldRemind = (settings: RowOf<typeof Settings>) => settings.shouldRemind;
command({
  callers: ["client"],
  input: { taskId: ref(Task), other: ref(Task).nullable() },
  emits: [],
  requires: { open: ({ refs }) => refs.taskId.completedAt === null },
}).decide(({ refs }) => {
  // @ts-expect-error refs holds only the records of required ref fields, which not-found guarantees
  refs.other;
  return refs.taskId.title === "" ? [] : [];
});
command({ callers: ["client"], emits: [] }).decide(({ records }) => {
  records.Task.filter(isOpen);
  shouldRemind(records.Settings);
  // @ts-expect-error RowOf records are readonly like expression records
  records.Task.map((task: RowOf<typeof Task>) => (task.title = ""));
  return [];
});

// Records are a Bag: no index, length or iterator, and a sort key is a number or a time.
query({ callers: ["client"], output: { n: z.number() } }).resolve(({ records }) => {
  // @ts-expect-error a Bag has no index
  void records.Task[0];
  // @ts-expect-error a Bag has no length
  void records.Task.length;
  // @ts-expect-error a Bag is not iterable
  for (const t of records.Task) void t;
  // @ts-expect-error a Bag has no find; filter and only() find one record
  records.Task.find(() => true);
  // @ts-expect-error a string is not a sort key
  records.Task.sortedBy((t) => t.title);
  // @ts-expect-error a nullable value is not a sort key
  records.Task.min((t) => t.dueAt);
  const due: Bag<number> = records.Task.map((t) => t.dueAt).filter((d) => d !== null);
  return { n: due.size };
});

// A bag output takes a Bag, and a sortedBy output takes Runs; an array output, whose order means something, takes no Bag.
query({ callers: ["client"], output: { ids: bag(ref(Task)) } }).resolve(({ records }) => ({
  ids: records.Task.map((t) => t.id),
}));
query({
  callers: ["client"],
  output: { tasks: sortedBy(z.object({ id: ref(Task), createdAt: instant }), "createdAt") },
}).resolve(({ records }) => ({
  tasks: records.Task.map((t) => ({ id: t.id, createdAt: t.createdAt })).sortedBy((t) => t.createdAt),
}));
query({ callers: ["client"], output: { ids: z.array(ref(Task)) } }).resolve(({ records }) => ({
  // @ts-expect-error an array output takes no Bag
  ids: records.Task.map((t) => t.id),
}));

// A bag, set or sortedBy value that spec code receives is a Bag or Runs, and spec code may give it back as it is.
query({
  callers: ["client"],
  input: { ids: set(ref(Task)), tasks: sortedBy(z.object({ id: ref(Task), createdAt: instant }), "createdAt") },
  output: { ids: bag(ref(Task)), earliest: bag(ref(Task)) },
  ensures: {
    // @ts-expect-error a received bag has no length
    counted: ({ output }) => output.ids.length > 0,
  },
}).resolve(({ input }) => ({ ids: input.ids, earliest: input.tasks[0]?.map((t) => t.id) ?? [] }));
machine({
  description: "",
  context: { ids: bag(z.string()).default([]) },
  receives: { taskAddedRecorded },
  initial: "a",
  states: { a: {} },
}).chart({
  states: {
    a: { on: { taskAddedRecorded: [{ assign: { ids: ({ context }) => context.ids.filter((id) => id !== "") } }] } },
  },
});

machine({
  description: "",
  context: { ids: z.array(z.string()).default([]) },
  receives: { taskAddedRecorded },
  initial: "a",
  states: { a: {} },
}).chart({
  states: {
    a: {
      on: {
        taskAddedRecorded: [
          {
            assign: {
              ids: ({ context, payload }) => {
                // @ts-expect-error expressions cannot mutate context arrays
                context.ids.push(payload.id);
                return [...context.ids, payload.id];
              },
            },
          },
        ],
      },
    },
  },
});

automation({ receives: { taskAdded }, commands: { addTask } }).send({
  input: ({ createKey }) => ({
    // @ts-expect-error createKey takes only a ref schema
    taskId: createKey(z.string()),
    title: "",
  }),
});

// An external service's command can have an output on acceptance, which ensures reads.
const charge = externalCommand({
  callers: [],
  input: { amount: z.number() },
  output: { chargeId: z.string() },
  emits: [],
  rejects: [],
  ensures: { hasId: ({ output }) => output.chargeId !== "" },
});

// accepted(output) answers a command with output, typed like fulfilled(output).
const chargeAccepted: AnswerOf<typeof charge> = accepted({ chargeId: "ch_1" });
// @ts-expect-error a command with output is accepted with it
const chargeAcceptedBare: AnswerOf<typeof charge> = accepted();
// @ts-expect-error the output has the command's output shape
const chargeAcceptedWrong: AnswerOf<typeof charge> = accepted({ chargeId: 1 });
void [chargeAccepted, chargeAcceptedBare, chargeAcceptedWrong];

// @ts-expect-error ensures of an external command without output cannot read output
externalCommand({ emits: [], rejects: [], ensures: { hasId: ({ output }) => output } });

// @ts-expect-error a spec service's command has no output (CQRS)
command({ callers: ["client"], output: { id: z.string() }, emits: [] });

machine({
  description: "",
  context: { chargeId: z.string().default("") },
  commands: { charge, addTask },
  initial: "charging",
  states: { charging: {}, adding: {} },
}).chart({
  states: {
    charging: {
      sends: {
        charge: {
          input: () => ({ amount: 1 }),
          // onAccepted reads the output of a command with output.
          onAccepted: [{ target: "adding", assign: { chargeId: ({ output }) => output.chargeId } }],
        },
      },
    },
    adding: {
      sends: {
        addTask: {
          input: () => ({ taskId: "task-1", title: "" }),
          // @ts-expect-error onAccepted of a command without output cannot read output
          onAccepted: [{ assign: { chargeId: ({ output }) => output } }],
          onRejected: [],
        },
      },
    },
  },
});

// @ts-expect-error an external service's query has no resolve
externalQuery({ output: { day: z.string() }, rejects: [] }).resolve(() => ({ day: "" }));

// @ts-expect-error an external service's command declares the kinds it may reject with
externalCommand({ emits: [] });

// @ts-expect-error a command of a spec service takes the kinds it may reject with from its definition
command({ callers: [], emits: [], rejects: [] }).decide(() => []);

const undecided = command({ callers: ["client"], input: { taskId: ref(Task) }, emits: [taskCompletedRecorded] });
// @ts-expect-error a non-external command is not a command until decide is given
contract({ undecided });

// @ts-expect-error query requires read only input
query({ callers: ["client"], output: { n: z.number() }, requires: { some: ({ records }) => records.Task.size > 0 } });

// Command ensures read, through bound, the values binds computed before the command ran.
command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [taskCompletedRecorded],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  ensures: { wasOpen: ({ bound }) => bound.task.completedAt === null },
}).decide(({ input, now }) => [emit(taskCompletedRecorded, { id: input.taskId, completedAt: now })]);

const renameTask = command({
  callers: ["client"],
  input: { taskId: ref(Task), title: Task.fields.title },
  emits: [],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: { changed: ({ input, bound }) => bound.task.title !== input.title },
}).decide(() => []);
machine({
  description: "",
  context: { n: z.number().default(0) },
  commands: { renameTask },
  initial: "a",
  states: { a: {} },
}).chart({
  states: {
    a: {
      sends: {
        renameTask: {
          input: () => ({ taskId: "task-1", title: "a" }),
          onAccepted: [],
          onRejected: [
            { guard: { unchanged: ({ rejection }) => rejection.kind === "requires" }, target: "a" },
            // @ts-expect-error onRejected's rejection has no reason
            { guard: { named: ({ rejection }) => rejection.reason === "changed" }, target: "a" },
            {},
          ],
        },
      },
    },
  },
});

machine({
  description: "",
  commands: { renameTask },
  initial: "a",
  states: { a: {}, b: {} },
}).chart({
  states: {
    a: {
      sends: {
        renameTask: {
          input: () => ({ taskId: "task-1", title: "a" }),
          onAccepted: [],
          // @ts-expect-error onRejected ends with a transition without a guard, so that every rejection is handled
          onRejected: [{ guard: { unchanged: ({ rejection }) => rejection.kind === "requires" }, target: "b" }],
        },
      },
    },
  },
});

command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [],
  // @ts-expect-error keys that read bound come after binds
  requires: { open: ({ bound }) => bound.task.completedAt === null },
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
}).decide(() => []);

automation({ receives: { dueChanged }, commands: { setReminder } }).send({
  // @ts-expect-error keys that read bound come after binds
  input: ({ payload, bound }) => ({ taskId: payload.id, remindAt: bound.dueAt }),
  binds: { dueAt: ({ payload }) => payload.dueAt },
});

const dueTasks = query({
  callers: ["client"],
  input: { from: instant, until: instant },
  output: {},
  requires: { fromBeforeUntil: ({ input }) => input.from < input.until },
}).resolve(() => ({}));

machine({
  description: "",
  queries: { dueTasks },
  initial: "a",
  states: { a: {} },
}).chart({
  states: {
    a: {
      calls: {
        dueTasks: {
          input: ({ now }) => ({ from: now, until: now }),
          onFulfilled: [],
          onRejected: [
            { guard: { reversed: ({ rejection }) => rejection.kind === "requires" }, target: "a" },
            // @ts-expect-error onRejected's rejection in calls has no reason
            { guard: { named: ({ rejection }) => rejection.reason === "fromBeforeUntil" }, target: "a" },
            {},
          ],
        },
      },
    },
  },
});

externalQuery({
  callers: [],
  output: { day: z.string() },
  rejects: [],
  // @ts-expect-error an external query's requires read only input
  requires: { some: ({ output }) => output.day !== "" },
});

// @ts-expect-error a command has no description
command({ callers: ["client"], description: "", emits: [] });

// @ts-expect-error a service has a description
service({ name: "test" });

// @ts-expect-error send has input when the command has input fields
automation({ receives: { taskAddedRecorded }, commands: { setReminder } }).send({});

// @ts-expect-error a contract holds no functions
contract({ helper: () => 1 });

// @ts-expect-error a contract holds no entities
contract({ Task });

// @ts-expect-error a contract holds no events that write records
contract({ taskAddedRecorded });

const todoContract = contract({ taskAdded, TaskId: ref(Task), TaskTitle: Task.fields.title });

// A contract carries the records of its service, as data, and whether tazuna runs the service's spec.
const taskRows: RecordsOf<typeof todoContract>["Task"][number]["title"] = "";
const settingsRow: RecordsOf<typeof todoContract>["Settings"]["shouldRemind"] = true;
const specKind: KindOf<typeof todoContract> = "spec";
void [taskRows, settingsRow, specKind];
const calendarContract = externalContract({});
// @ts-expect-error an external contract carries no records
void ({} as RecordsOf<typeof calendarContract>)["Task"];
const externalKind: KindOf<typeof calendarContract> = "external";
void externalKind;

const notify = externalCommand({ callers: [], input: { text: z.string() }, emits: [], rejects: ["unavailable"] });

// An automation ignores an unavailable rejection with onRejected: [].
automation({ receives: { taskAdded }, commands: { notify } }).send({ input: () => ({ text: "" }), onRejected: [] });

automation({ receives: { taskAdded }, commands: { notify } }).send({
  input: () => ({ text: "" }),
  // @ts-expect-error an automation's onRejected only ignores
  onRejected: [{}],
});

// @ts-expect-error an automation receives exactly one event
automation({ receives: { dueChanged, taskAddedRecorded }, commands: { setReminder } });

// @ts-expect-error an automation calls no query; a reaction that waits for an answer is a machine
automation({ receives: { taskAddedRecorded }, commands: { addTask }, queries: { tasks } });

machine({ description: "", context: { n: z.number().default(0) }, initial: "a", states: { a: {} } }).chart({
  // @ts-expect-error a machine without receives has no on keys
  on: { taskAddedRecorded: [{ target: "a" }] },
});

machine({
  description: "",
  context: { n: z.number().default(0) },
  receives: { taskCompletedRecorded },
  initial: "a",
  states: { a: {} },
}).chart({
  // @ts-expect-error on keys name receives
  on: { taskAddedRecorded: [{ target: "a" }] },
});

machine({
  description: "",
  context: { n: z.number().default(0) },
  receives: { taskCompletedRecorded },
  initial: "a",
  states: { a: {}, b: {} },
}).chart({
  states: {
    a: {
      on: {
        // @ts-expect-error assign keys name context fields
        taskCompletedRecorded: [{ assign: { m: () => 1 } }],
      },
    },
    // @ts-expect-error target names a state
    b: { always: [{ target: "zz" }] },
  },
});

machine({
  description: "",
  context: { side: z.enum(["left", "right"]).default("left") },
  initial: "a",
  states: { a: {} },
}).chart({
  // A string literal returned by an argumentless expression is not widened to string.
  states: { a: { always: [{ guard: { never: () => false }, assign: { side: () => "right" } }] } },
});

machine({
  description: "",
  context: { count: z.number().default(0) },
  queries: { tasks, reminderSettings },
  commands: { addTask },
  initial: "checking",
  states: { checking: {}, adding: {}, noInput: {}, unknown: {}, idle: {} },
  invariants: {
    // @ts-expect-error active keys name states
    typo: ({ active }) => !active.idel,
  },
}).chart({
  states: {
    checking: {
      calls: {
        tasks: {
          input: () => ({ filter: "open" }),
          onFulfilled: [
            { guard: { many: ({ output }) => output.tasks.size > 3 }, target: "adding" },
            { assign: { count: ({ output }) => output.tasks.size }, target: "idle" },
          ],
          onRejected: [],
        },
        reminderSettings: { onFulfilled: [] },
      },
    },
    adding: {
      sends: {
        addTask: {
          // @ts-expect-error sends input matches the command's input schema
          input: () => ({ taskId: "task-1" }),
          onAccepted: [],
          onRejected: [],
        },
      },
    },
    // @ts-expect-error calls has input when the query has input fields
    noInput: { calls: { tasks: { onFulfilled: [], onRejected: [] } } },
    // @ts-expect-error calls keys name queries
    unknown: { calls: { taskz: { onFulfilled: [], onRejected: [] } } },
  },
});

const dueScreen = screen({
  description: "",
  input: { from: instant, until: instant },
  output: { choice: z.object({ dueAt: instant }).nullable() },
  initial: "closed",
  states: { closed: { type: "final" } },
}).chart({ resolve: () => ({ choice: null }) });

screen({
  description: "",
  context: { side: z.enum(["left", "right"]).default("left"), done: z.boolean().default(false) },
  receives: { taskAddedRecorded },
  queries: { tasks },
  screens: { due: dueScreen },
  controls: { pick: { label: "Pick", payload: { side: z.enum(["left", "right"]) } } },
  initial: "a",
  states: { a: {}, b: {}, c: {} },
}).chart({
  offers: { pick: () => [{ side: "left" }] },
  states: {
    a: {
      on: {
        pick: [{ assign: { side: ({ payload }) => payload.side } }],
        taskAddedRecorded: [{ guard: { named: ({ payload }) => payload.title !== "" }, target: "b" }],
      },
      shows: { tasks: { input: () => ({ filter: "all" }) } },
    },
    b: {
      opens: {
        due: {
          modal: true,
          input: ({ now }) => ({ from: now, until: now }),
          onDone: [{ assign: { done: ({ output }) => output.choice !== null }, target: "a" }],
        },
      },
    },
    // @ts-expect-error opens keys name screens
    c: { opens: { dew: { input: ({ now }) => ({ from: now, until: now }), onDone: [] } } },
  },
});

screen({
  description: "",
  receives: { taskAddedRecorded },
  // @ts-expect-error control names do not clash with receives names
  controls: { taskAddedRecorded: { label: "Add" } },
  initial: "a",
  states: { a: {} },
}).chart({ offers: { taskAddedRecorded: any } });

screen({
  description: "",
  output: { completed: z.boolean() },
  initial: "end",
  states: { end: { type: "final" } },
}).chart({
  // @ts-expect-error resolve returns a value matching the screen's output schema
  resolve: () => ({ completed: 1 }),
});
screen({ description: "", output: { completed: z.boolean() }, initial: "end", states: { end: { type: "final" } } })
  // @ts-expect-error a screen with output fields has resolve
  .chart({});
screen({ description: "", initial: "end", states: { end: { type: "final" } } }).chart({
  // @ts-expect-error a screen without output fields has no resolve
  resolve: () => ({}),
});
screen({
  description: "",
  input: { count: z.number() },
  output: { picked: z.number() },
  initial: "end",
  states: { end: { type: "final" } },
  // @ts-expect-error screen requires read only input
  requires: { picked: ({ output }) => output.picked > 0 },
  ensures: { belowCount: ({ input, output }) => output.picked < input.count },
}).chart({ resolve: ({ input }) => ({ picked: input.count - 1 }) });

machine({
  description: "",
  queries: { tasks },
  initial: "a",
  states: { a: {} },
}).chart({
  // A string literal returned by an argumentless expression is not widened to string.
  states: { a: { calls: { tasks: { input: () => ({ filter: "open" }), onFulfilled: [], onRejected: [] } } } },
});

machine({ description: "", receives: { taskAddedRecorded }, initial: "a", states: { a: {}, b: {} } }).chart({
  states: {
    a: {
      on: {
        taskAddedRecorded: [
          // Machine expressions read their own service's records through records.
          { guard: { enabled: ({ records }) => records.Settings.shouldRemind }, target: "b" },
          // @ts-expect-error records keys name the service's entities
          { guard: { typo: ({ records }) => records.Tasks.size > 0 }, target: "b" },
        ],
      },
    },
    b: { on: { taskAddedRecorded: [{ target: "a" }] } },
  },
});

automation({ receives: { taskAddedRecorded }, commands: { setReminder } }).send({
  // Automation expressions read their own service's records through records.
  guard: { enabled: ({ records }) => records.Settings.shouldRemind },
  input: ({ payload, records }) => ({
    taskId: payload.id,
    remindAt: records.Task.get(payload.id)?.createdAt ?? now,
  }),
});

// initialContext sets a screen's context fields without defaults from input.
screen({
  description: "",
  input: { title: z.string() },
  context: { title: z.string(), n: z.number().default(0) },
  initial: "a",
  states: { a: {} },
}).chart({ initialContext: ({ input }) => ({ title: input.title }) });
// @ts-expect-error context fields without defaults require initialContext
screen({ description: "", context: { title: z.string() }, initial: "a", states: { a: {} } }).chart({});
screen({ description: "", context: { title: z.string() }, initial: "a", states: { a: {} } }).chart({
  // @ts-expect-error initialContext returns the fields without defaults
  initialContext: () => ({}),
});
screen({ description: "", context: { title: z.string() }, initial: "a", states: { a: {} } }).chart({
  // @ts-expect-error initialContext returns no fields outside the schema
  initialContext: () => ({ title: "t", extra: 1 }),
});

// An after deadline has one of delay or at, and onFired.
machine({ description: "", initial: "a", states: { a: {}, b: {} } }).chart({
  states: {
    a: {
      after: {
        minute: { delay: 60_000, onFired: [{ target: "b" }] },
        created: {
          at: ({ records }) => (records.Task.min((t) => t.createdAt) ?? 0) + 60_000,
          onFired: [{ target: "b" }],
        },
        // @ts-expect-error at does not read now; a fixed length from now is a delay
        fromNow: { at: ({ now }) => now + 60_000, onFired: [{ target: "b" }] },
        // @ts-expect-error delay and at together
        both: { delay: 60_000, at: () => 0, onFired: [{ target: "b" }] },
        // @ts-expect-error neither delay nor at
        neither: { onFired: [{ target: "b" }] },
        // @ts-expect-error no onFired
        noTransitions: { delay: 60_000 },
      },
    },
  },
});

// A delay is a number of milliseconds, such as a duration constant.
machine({ description: "", initial: "a", states: { a: {}, b: {} } }).chart({
  states: {
    a: {
      after: {
        // @ts-expect-error a delay is milliseconds, not units
        units: { delay: { hours: 1 }, onFired: [{ target: "b" }] },
      },
    },
  },
});

// A state reads its own parameters as held, typed by their schemas; other states cannot.
machine({
  description: "",
  context: { last: z.string().default("") },
  receives: { taskAddedRecorded },
  initial: "idle",
  states: { idle: {}, tracking: { held: { last: z.string() } } },
}).chart({
  states: {
    idle: {
      // @ts-expect-error another state's held is not readable
      entry: { assign: { last: ({ held }) => held.last } },
      on: { taskAddedRecorded: [{ target: "tracking", with: { last: ({ context }) => context.last } }] },
    },
    tracking: { entry: { assign: { last: ({ held }) => held.last.toUpperCase() } } },
  },
});
// @ts-expect-error a held schema does not accept null
machine({ description: "", initial: "b", states: { a: { held: { x: z.number().nullable() } }, b: {} } });
// @ts-expect-error a held schema does not accept undefined
machine({ description: "", initial: "b", states: { a: { held: { x: z.number().optional() } }, b: {} } });
machine({
  description: "",
  initial: "p",
  // @ts-expect-error only an atomic state has held, since only it is the target of one edge
  states: { p: { held: { x: z.number() }, initial: "c", states: { c: {} } } },
});
machine({
  description: "",
  initial: "p",
  // @ts-expect-error a region has no held, since entering the parallel state enters it without an edge
  states: { p: { type: "parallel", states: { r: { held: { x: z.number() } }, s: {} } } },
});
// @ts-expect-error the chart's initial state has no held, since the chart enters it without an edge
machine({ description: "", initial: "a", states: { a: { held: { x: z.number() } }, b: {} } });
// @ts-expect-error a final state has no held
machine({ description: "", initial: "b", states: { p: { type: "final", held: { x: z.number() } }, b: {} } });
machine({
  description: "",
  initial: "p",
  // @ts-expect-error a history state has no held
  states: { p: { initial: "a", states: { a: {}, back: { type: "history", held: { x: z.number() } } } } },
});

// The transition that enters a state with held fills every parameter with `with`, of the schema's type.
const held2 = machine({
  description: "",
  receives: { taskAddedRecorded },
  initial: "b",
  states: { a: { held: { x: z.number(), y: z.number() } }, b: {} },
});
held2.chart({ states: { b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => 1, y: () => 2 } }] } } } });
held2.chart({
  // @ts-expect-error a target with held needs with
  states: { b: { on: { taskAddedRecorded: [{ target: "a" }] } } },
});
held2.chart({
  // @ts-expect-error with covers every held name
  states: { b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => 1 } }] } } },
});
held2.chart({
  // @ts-expect-error with has no names outside held
  states: { b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => 1, y: () => 2, z: () => 3 } }] } } },
});
held2.chart({
  // @ts-expect-error with returns values of the held schema's type
  states: { b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => "1", y: () => 2 } }] } } },
});
held2.chart({
  // @ts-expect-error a target without held has no with
  states: { a: { on: { taskAddedRecorded: [{ target: "b", with: { x: () => 1 } }] } } },
});
// @ts-expect-error a targetless transition has no with
held2.chart({ states: { b: { on: { taskAddedRecorded: [{ with: { x: () => 1, y: () => 2 } }] } } } });
// A held state targets itself with `with` only when it exits and enters again; otherwise it keeps its parameters.
held2.chart({
  states: {
    b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => 1, y: () => 2 } }] } },
    a: {
      on: {
        taskAddedRecorded: [
          { guard: { once: () => true }, target: "a", reenter: true, with: { x: () => 3, y: () => 4 } },
          { target: "a", reenter: false },
        ],
      },
    },
  },
});
held2.chart({
  states: {
    b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => 1, y: () => 2 } }] } },
    // @ts-expect-error without reenter the state is not entered again, so no with fills it
    a: { on: { taskAddedRecorded: [{ target: "a", reenter: false, with: { x: () => 3, y: () => 4 } }] } },
  },
});
held2.chart({
  states: {
    b: { on: { taskAddedRecorded: [{ target: "a", with: { x: () => 1, y: () => 2 } }] } },
    // @ts-expect-error reenter enters the state again, so with fills it
    a: { on: { taskAddedRecorded: [{ target: "a", reenter: true }] } },
  },
});

// A parent whose initial child has held fills it with `initial: { with }`; a map state's `with` reads the copy's key.
machine({
  description: "",
  initial: "p",
  states: {
    p: { initial: "a", states: { a: { held: { x: z.number() } } } },
    m: { type: "map", key: { rowId: z.string() }, initial: "w", states: { w: { held: { id: z.string() } } } },
  },
}).chart({
  states: {
    p: { initial: { with: { x: () => 1 } } },
    m: { items: () => [], initial: { with: { id: ({ key }) => key.rowId } } },
  },
});
machine({ description: "", initial: "p", states: { p: { initial: "a", states: { a: { held: { x: z.number() } } } } } })
  // @ts-expect-error the parent of a held initial child writes its initial edge
  .chart({ states: { a: { always: [] } } });
machine({ description: "", initial: "p", states: { p: { initial: "a", states: { a: {} } } } }).chart({
  // @ts-expect-error a parent whose initial child has no held has no initial edge
  states: { p: { initial: { with: { x: () => 1 } } } },
});

// held has the schema's type; with may still return null or undefined (Fault.heldSchema reports it).
machine({
  description: "",
  context: { mode: z.enum(["normal", "slowed"]).nullable().default(null) },
  receives: { taskAddedRecorded },
  initial: "b",
  states: { a: { held: { mode: z.literal("slowed") } }, b: {} },
}).chart({
  states: {
    a: {
      always: [
        {
          guard: {
            slowed: ({ held }) => {
              const mode: "slowed" = held.mode;
              return mode === "slowed";
            },
          },
          target: "b",
        },
      ],
    },
    b: {
      on: {
        taskAddedRecorded: [
          { target: "a", with: { mode: ({ context }) => (context.mode === "slowed" ? context.mode : null) } },
        ],
      },
    },
  },
});

// A state with children has initial, except a parallel state, which enters all children.
machine({
  description: "",
  initial: "a",
  states: {
    // @ts-expect-error a state with children has initial
    a: { states: { b: {}, c: {} } },
  },
});
machine({
  description: "",
  initial: "a",
  states: {
    // @ts-expect-error a parallel state has no initial
    a: { type: "parallel", initial: "b", states: { b: {}, c: {} } },
  },
});
machine({
  description: "",
  initial: "p",
  states: {
    // @ts-expect-error a nested initial names a child of that state
    p: { initial: "q", states: { a: {} } },
    q: {},
  },
});
// @ts-expect-error state names are unique in the tree
machine({ description: "", initial: "p", states: { p: { initial: "a", states: { a: {} } }, a: {} } });

// Body states refer to contract states by name at any depth; states without behavior are left out.
machine({ description: "", initial: "a", states: { a: {}, b: {} } }).chart({
  // @ts-expect-error a body state names a state in the tree
  states: { a: { always: [] }, c: { always: [] } },
});
machine({
  description: "",
  initial: "p",
  states: { p: { initial: "a", states: { a: {}, back: { type: "history" } } } },
}).chart({
  // @ts-expect-error a history state has no behavior
  states: { back: { always: [] } },
});
machine({ description: "", initial: "a", states: { a: {}, b: {} } }).chart({
  // @ts-expect-error a state without children has no onDone
  states: { a: { onDone: [{ target: "b" }] } },
});
machine({
  description: "",
  receives: { taskAddedRecorded },
  initial: "a",
  states: { a: {}, done: { type: "final" } },
}).chart({
  // @ts-expect-error a final state has only entry
  states: { done: { on: { taskAddedRecorded: [{ target: "a" }] } } },
});

// offers returns control payloads; a control without payload fields returns [{}] or [].
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { title: z.string() } }, close: { label: "Close" } },
  initial: "open",
  states: { open: {} },
}).chart({
  // @ts-expect-error offers returns payload-shaped values
  offers: { pick: () => [{ name: "x" }] },
});
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { title: z.string() } }, close: { label: "Close" } },
  initial: "open",
  states: { open: {} },
}).chart({
  offers: { pick: any, close: () => [{}] },
});
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { title: z.string() } }, close: { label: "Close" } },
  initial: "open",
  states: { open: {} },
}).chart({
  // @ts-expect-error the chart's own offers name every control
  offers: { close: any },
});
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { title: z.string() } } },
  initial: "open",
  states: { open: {} },
}).chart({
  // @ts-expect-error offers keys name controls
  offers: { close: none },
});

// State offers read held and, in map copies, key like other state expressions; a final state has no offers.
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { rowId: z.string() } } },
  initial: "rows",
  states: {
    open: { held: { title: z.string() } },
    rows: { type: "map", key: { rowId: z.string() }, initial: "idle", states: { idle: {} } },
    closed: { type: "final" },
  },
}).chart({
  states: {
    open: { offers: { pick: ({ held }) => (held.title === "" ? [] : [{ rowId: "a" }]) } },
    rows: { items: () => [] },
    idle: { offers: { pick: ({ key }) => [key] } },
    // @ts-expect-error a final state has only entry
    closed: { offers: { pick: none } },
  },
});
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { rowId: z.string() } } },
  initial: "open",
  states: { open: {} },
}).chart({
  // @ts-expect-error state offers also return payload-shaped values
  states: { open: { offers: { pick: () => [{ name: "x" }] } } },
});

// Only command input and assign read createKey; only transitions with a target have reenter.
machine({
  description: "",
  context: { last: z.string().default("") },
  receives: { taskAddedRecorded },
  initial: "a",
  states: { a: {} },
}).chart({
  states: {
    a: {
      on: {
        taskAddedRecorded: [
          {
            guard: { fresh: ({ payload }) => payload.title !== "" },
            assign: { last: ({ createKey }) => createKey(ref(Task)) },
          },
          // @ts-expect-error createKey takes a ref schema, not an entity
          { assign: { last: ({ createKey }) => createKey(Task) } },
          // @ts-expect-error guard does not read createKey
          { guard: { fresh: ({ createKey }) => createKey(ref(Task)) !== "" } },
          // @ts-expect-error a transition without target has no reenter
          { reenter: true },
          { target: "a", reenter: true },
        ],
      },
    },
  },
});

// The chart's offers name every control.
screen({
  description: "",
  controls: { pick: { label: "Pick", payload: { title: z.string() } } },
  initial: "a",
  states: { a: {} },
}).chart({
  // @ts-expect-error offers lacks pick
  offers: {},
});

// @ts-expect-error constants values have the schema's input type
constants({ service: "types", schema: z.object({ limit: z.int() }), values: { limit: "10" } });

// A contract can hold the object that a constants() call returns.
contract({ limits: constants({ service: "types", schema: z.object({ limit: z.int() }), values: { limit: 10 } }) });

// @ts-expect-error a contract holds no object not made by constants()
contract({ limits: { limit: 10 } });

// A bag constant stays an array, since an implementation reads constants too.
void constants({ service: "types", schema: z.object({ tags: bag(z.string()) }), values: { tags: ["a"] } }).tags.length;

// A sortedBy key is a number or date field.
sortedBy(z.strictObject({ n: z.int(), at: instant, on: date }), "on");

// @ts-expect-error a sortedBy key is not a string field, since string order differs by language
sortedBy(z.strictObject({ title: z.string() }), "title");

const cents = z.codec(z.string(), z.int(), { decode: Number, encode: String });
// @ts-expect-error a sortedBy key has no codec, since a codec may decode to another order
sortedBy(z.strictObject({ price: cents }), "price");

// Map copy expressions read key, the copy context and the instance context; assign writes to each.
machine({
  description: "",
  context: { count: z.number().default(0) },
  receives: { taskAddedRecorded },
  commands: { setReminder },
  initial: "idle",
  states: {
    idle: {},
    reminding: {
      type: "map",
      key: { id: ref(Task) },
      context: { remindAt: instant.nullable().default(null) },
      initial: "waiting",
      states: { waiting: {}, setting: {} },
    },
  },
  invariants: {
    // @ts-expect-error invariants' active has no copy states
    notWaiting: ({ active }) => !active.waiting,
  },
}).chart({
  states: {
    idle: {
      on: {
        taskAddedRecorded: [
          { target: "reminding" },
          // @ts-expect-error a transition outside the copies cannot target a copy state
          { target: "waiting" },
        ],
      },
      // @ts-expect-error an expression outside the copies cannot read key
      always: [{ guard: { keyed: ({ key }) => key !== "" }, target: "reminding" }],
    },
    reminding: { items: ({ records }) => records.Task.map((t) => ({ id: t.id })) },
    waiting: {
      on: {
        taskAddedRecorded: [
          {
            target: "setting",
            assign: { remindAt: ({ payload }) => payload.createdAt, count: ({ context }) => context.count + 1 },
          },
          // @ts-expect-error a copy transition cannot target a state outside the copies
          { target: "idle" },
        ],
      },
    },
    setting: {
      sends: {
        setReminder: {
          input: ({ key, context, now }) => ({ taskId: key.id, remindAt: context.remindAt ?? now }),
          onAccepted: [],
          onRejected: [],
        },
      },
    },
  },
});

const reminding = {
  type: "map",
  key: { taskId: ref(Task) },
  initial: "waiting",
  states: { waiting: {} },
} as const;
machine({ description: "", initial: "reminding", states: { reminding } }).chart({
  // @ts-expect-error items returns rows holding the key fields
  states: { reminding: { items: () => ["task-1"] } },
});
// @ts-expect-error a map state has items in the body
machine({ description: "", initial: "reminding", states: { reminding } }).chart({});
// @ts-expect-error copy context field names do not clash with instance context field names
machine({
  description: "",
  context: { remindAt: instant.nullable().default(null) },
  initial: "reminding",
  states: { reminding: { ...reminding, context: { remindAt: instant.nullable().default(null) } } },
});
// @ts-expect-error a map state has no map state below it
machine({
  description: "",
  initial: "reminding",
  states: {
    reminding: {
      ...reminding,
      initial: "inner",
      states: { inner: { type: "map", key: { taskId: ref(Task) }, initial: "leaf", states: { leaf: {} } } },
    },
  },
});
// @ts-expect-error a map state has no final state below it
machine({
  description: "",
  initial: "reminding",
  states: { reminding: { ...reminding, states: { waiting: { type: "final" } } } },
});
// @ts-expect-error a map state has no held
machine({ description: "", initial: "reminding", states: { reminding: { ...reminding, held: { x: z.number() } } } });

// A screen map state's items read shown; copy on reacts to controls and received events.
const rowsScreen = screen({
  description: "",
  receives: { taskDeleted },
  queries: { tasks },
  commands: { completeTask },
  screens: { taskDetail: taskDetailScreen },
  controls: {
    complete: { label: "", payload: { taskId: ref(Task) } },
    add: { label: "", payload: { title: z.string() } },
  },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "idle",
      states: { idle: {}, completing: {} },
    },
  },
  invariants: {
    // @ts-expect-error screen invariants' active has no copy states
    notIdle: ({ active }) => !active.idle,
  },
});
rowsScreen.chart({
  offers: { complete: any, add: any },
  states: {
    rows: { items: ({ shown }) => (shown.tasks?.tasks ?? []).map((t) => ({ taskId: t.taskId })) },
    idle: {
      on: {
        complete: [{ target: "completing" }],
        add: [{ target: "completing" }],
        taskDeleted: [{ target: "completing" }],
      },
    },
    completing: {
      sends: {
        completeTask: {
          input: ({ key }) => ({ taskId: key.taskId }),
          onAccepted: [{ target: "idle" }],
          onRejected: [],
        },
      },
    },
  },
});
rowsScreen.chart({
  offers: { complete: any, add: any },
  states: {
    rows: { items: () => [] },
    // @ts-expect-error a copy state opens no child screen
    idle: { opens: { taskDetail: { input: () => ({ taskId: "task-1", placeholderTitle: "" }), onDone: [] } } },
  },
});
rowsScreen.chart({
  offers: { complete: any, add: any },
  states: {
    rows: { items: () => [] },
    // @ts-expect-error a copy state shows no query
    idle: { shows: { tasks: { input: () => ({ filter: "all" }) } } },
  },
});
// @ts-expect-error screen copy context field names do not clash with screen context field names
screen({
  description: "",
  context: { remindAt: instant.nullable().default(null) },
  initial: "reminding",
  states: { reminding: { ...reminding, context: { remindAt: instant.nullable().default(null) } } },
});

// A unit is a sanctioned ECMA-402 single unit or two of them joined by -per-.
z.number().meta({ unit: "kilometer-per-hour" });
// @ts-expect-error a unit is an ECMA-402 unit identifier, not a plural
z.int().meta({ unit: "minutes" });
// @ts-expect-error a unit is an ECMA-402 unit identifier, not an abbreviation
z.number().meta({ unit: "km/h" });

// active has the states outside the region or map state that holds the expression; invariants read every state
// outside the copies.
const leftIsOn = ({ active }: { readonly active: { readonly leftOn: boolean } }) => active.leftOn;
machine({
  description: "",
  receives: { taskAddedRecorded },
  initial: "both",
  states: {
    both: {
      type: "parallel",
      states: {
        left: { initial: "leftOff", states: { leftOff: {}, leftOn: {} } },
        right: { initial: "rightOff", states: { rightOff: {}, rightOn: {} } },
        tasks: { type: "map", key: { id: ref(Task) }, initial: "waiting", states: { waiting: {}, seen: {} } },
      },
    },
  },
  invariants: { leftOnWhileBoth: ({ active }) => active.both || !active.leftOn },
}).chart({
  on: {
    // @ts-expect-error an expression outside the states reads no state
    taskAddedRecorded: [{ guard: { both: ({ active }) => active.both } }],
  },
  states: {
    // @ts-expect-error a state that no region or map state holds reads no state
    both: { on: { taskAddedRecorded: [{ guard: { leftOn: ({ active }) => active.leftOn } }] } },
    leftOff: {
      on: {
        taskAddedRecorded: [
          { guard: { rightOn: ({ active }) => active.rightOn } },
          // @ts-expect-error a state does not read the region or map state that holds it
          { guard: { leftOn: ({ active }) => active.leftOn } },
          // @ts-expect-error nor through a function
          { guard: { leftIsOn } },
        ],
      },
    },
    // @ts-expect-error the parallel state's child is the region itself
    leftOn: { on: { taskAddedRecorded: [{ guard: { left: ({ active }) => active.left } }] } },
    tasks: { items: ({ records }) => records.Task.map((t) => ({ id: t.id })) },
    waiting: {
      on: {
        taskAddedRecorded: [
          { guard: { leftOn: ({ active }) => active.leftOn } },
          // @ts-expect-error a copy's states are held by their map state
          { guard: { seen: ({ active }) => active.seen } },
        ],
      },
    },
  },
});

screen({
  description: "",
  output: { isClosed: z.boolean() },
  controls: { close: { label: "Close" } },
  initial: "list",
  states: { list: {}, closed: { type: "final" } },
}).chart({
  offers: { close: any },
  // @ts-expect-error an expression outside the states reads no state
  resolve: ({ active }) => ({ isClosed: active.closed }),
  states: { list: { on: { close: [{ target: "closed" }] } } },
});

// A service name holds none of the characters that separate the parts of generated names (reservedNameCharacter).
// @ts-expect-error a trace name would read todo.tasks as the service todo
service({ name: "todo.tasks", description: "" });
// @ts-expect-error a created key would read a/b as two parts
externalService({ name: "a/b", description: "" });

// Given lists the peers, the own service among none of them, and When names each by its service's name.
scenarioOfScreens({
  description: "types",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: {},
    peers: [external(calendarPeer), skip(devicePeer, "the screens never reach the device")],
  },
  when: (w) => {
    void w.peer.calendar;
    // @ts-expect-error a peer is named by its service's name
    void w.peer.cal;
    return {};
  },
  then: () => [],
});
scenarioOfScreens({
  description: "types",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: {},
    // @ts-expect-error the own service is no peer (unknownPeer)
    peers: [skip(screensPeer, "the own service")],
  },
  when: () => ({}),
  then: () => [],
});

// A line names only messages between the own service and the peers that Given lists as running or external.
scenarioOfScreens({
  description: "types",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: {},
    peers: [
      run(todoPeer, { Task: [], Settings: { shouldRemind: true } }),
      external(calendarPeer),
      skip(devicePeer, "the screens never reach the device in this scenario"),
    ],
  },
  when: (w) => {
    const adding = w.client.as("client").send(todoPeer.addTask, { taskId: "task-1", title: "Buy milk" });
    adding.request(calendarPeer.nextBusinessDay);
    // @ts-expect-error the device is skipped: no message to it is named
    adding.request(devicePeer.requestNotificationPermission);
    // @ts-expect-error a skipped peer has no actor
    w.peer.device;
    // @ts-expect-error a peer that Given does not list has no actor
    w.peer.notifier;
    // @ts-expect-error the client reaches the own service and running peers only
    w.client.as("client").send(devicePeer.requestNotificationPermission, {});
    // @ts-expect-error a running peer sends only to the own service and the listed peers
    w.peer.todo.send(devicePeer.showNotification, { text: "Due" });
    return { adding };
  },
  then: ({ adding }) => [
    // Then states a request to a skipped peer: the own service sends it, though nobody receives it.
    requested(adding, [requestOf(devicePeer.requestNotificationPermission, {})]),
  ],
});

// The scenario grammar: what a line names and writes.
scenarioOfScreens({
  description: "types",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: {},
    peers: [run(todoPeer, { Task: [], Settings: { shouldRemind: true } }), external(calendarPeer)],
  },
  when: (w) => {
    const list = w.startup.screen(taskListScreen);
    const watching = w.startup.subscription(todoPeer.tasks);
    const look = w.user.look(list);
    const adding = w.client.as("client").send(todoPeer.addTask, { taskId: "task-1", title: "Buy milk" });
    const asking = adding.request(calendarPeer.nextBusinessDay);
    w.net.deliver(adding.request(calendarPeer.nextBusinessDay, { after: parseInstant("2026-10-25T10:00:00+09:00") }));
    // @ts-expect-error a pick has fields of the input only
    void adding.request(calendarPeer.nextBusinessDay, { input: { after: parseInstant("2026-10-25T10:00:00+09:00") } });
    // @ts-expect-error the client reaches running services only, not an external peer
    w.client.as("client").call(calendarPeer.nextBusinessDay, { after: parseInstant("2026-10-25T10:00:00+09:00") });
    // @ts-expect-error a client line reaches its receiver directly; no message is delivered
    w.net.deliver(adding);
    // @ts-expect-error only a request can fail
    w.net.refuse(adding.event(todoPeer.taskAdded));
    // @ts-expect-error a look line carries no message
    w.net.leaveInFlight(look);
    // @ts-expect-error created() is written only in a running peer's message
    w.client.as("client").send(todoPeer.completeTask, { taskId: created() });
    // @ts-expect-error an external peer's values are its own, never created()
    w.peer.calendar.answer(asking, { result: "fulfilled", output: { day: created() } });
    const sent = w.peer.todo.send(todoPeer.completeTask, { taskId: created() });
    // @ts-expect-error the client resends only its own lines
    w.client.resend(sent);
    // @ts-expect-error an observed value is no string
    w.client.as("client").send(todoPeer.addTask, { taskId: "task-2", title: `${asking.input.from}` });
    // @ts-expect-error an observed value is not compared
    if (asking.input.from === "2026-10-25") w.host.restart();
    // @ts-expect-error an observed value is not spread
    w.client.as("client").call(todoPeer.tasks, { ...watching.input });
    const listed = w.client.as("client").call(todoPeer.tasks, { filter: "all" });
    w.client.as("client").call(todoPeer.taskDetail, { taskId: adding.request(todoPeer.addTask).input.taskId });
    // @ts-expect-error a bag's elements have no position: name one by content or by the line that sent it
    w.client.as("client").send(todoPeer.completeTask, { taskId: listed.output.tasks[0].taskId });
    w.client.as("client").send(todoPeer.addTask, raw({ taskId: "task-3", title: 7 }));
    const completing = w.client.as("client").send(todoPeer.completeTask, { taskId: "task-1" });
    const subscribed = w.client.as("client").subscribe(todoPeer.tasks, { filter: "all" });
    return { look, watching, adding, completing, subscribed };
  },
  then: ({ look, watching, adding, completing, subscribed }) => [
    // @ts-expect-error a look line's processing emits nothing
    emitted(look, []),
    // @ts-expect-error endOf takes a subscription, not a command
    requested(adding, [endOf(adding.request(calendarPeer.nextBusinessDay))]),
    requested(adding, [requestOf(calendarPeer.nextBusinessDay, { after: parseInstant("2026-10-25T10:00:00+09:00") })]),
    // @ts-expect-error Then states requests only to the peers that Given lists
    requested(adding, [requestOf(devicePeer.requestNotificationPermission, {})]),
    // @ts-expect-error Then states only the own service's events
    emitted(adding, [eventOf(todoPeer.taskAdded, { taskId: "task-1" })]),
    requested(adding, [endOf(watching)]),
    answered(completing, rejected("requires", "notCompleted")),
    answered(completing, rejected("requires")),
    answered(completing, rejected("not-found")),
    answered(completing, accepted()),
    // @ts-expect-error a command without output is accepted without one
    answered(completing, accepted({ taskId: "task-1" })),
    // @ts-expect-error a requires rejection names a requires condition of the command
    answered(completing, rejected("requires", "notCompleteddd")),
    // @ts-expect-error only a requires rejection has a reason
    answered(completing, rejected("not-found", "notCompleted")),
    // @ts-expect-error a rejection kind is one of RejectionKind
    answered(completing, rejected("missing")),
    // @ts-expect-error a command is accepted, not fulfilled
    answered(completing, fulfilled({ taskId: "task-1" })),
    answered(subscribed, [fulfilled({ tasks: [] })]),
    // @ts-expect-error a subscription's answers are a list
    answered(subscribed, fulfilled({ tasks: [] })),
    // @ts-expect-error an output has the query's output shape
    answered(subscribed, [fulfilled({ tasks: [{ taskId: 1 }] })]),
  ],
});

// An event line's resultOf names the request of a command.
scenarioOfTodo({
  description: "types",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: { Task: [], Settings: { shouldRemind: true } },
    peers: [external(calendarPeer), external(devicePeer)],
  },
  when: (w) => {
    const adding = w.client.as("client").send(todoPeer.addTask, { taskId: "task-1", title: "Buy milk" });
    const asking = adding.request(devicePeer.requestNotificationPermission);
    w.net.deliver(asking);
    w.peer.device.emit(devicePeer.notificationPermissionGranted, {}, { resultOf: asking });
    const asked = adding.request(calendarPeer.nextBusinessDay);
    // @ts-expect-error a query has no result events
    w.peer.device.emit(devicePeer.notificationPermissionGranted, {}, { resultOf: asked });
    return {};
  },
  then: () => [],
});

// A shared Given is checked where it is written, and its steps place lines with its services and the own service.
const withTodo = givenOfScreens({
  start: parseInstant("2026-10-25T10:00:00+09:00"),
  records: {},
  peers: [run(todoPeer, { Task: [], Settings: { shouldRemind: true } }), external(calendarPeer)],
});
// @ts-expect-error a start is milliseconds since the epoch
givenOfScreens({ start: "yesterday", records: {}, peers: [] });
givenOfScreens({
  start: parseInstant("2026-10-25T10:00:00+09:00"),
  records: {},
  // @ts-expect-error the own service is no peer (unknownPeer)
  peers: [skip(screensPeer, "the own service")],
});
givenOfScreens({
  start: parseInstant("2026-10-25T10:00:00+09:00"),
  records: {},
  // @ts-expect-error a service is a peer once, in one role
  peers: [external(calendarPeer), skip(calendarPeer, "listed twice")],
});
const addMilk = withTodo.step((w, title: string) =>
  w.client.as("client").send(todoPeer.addTask, { taskId: "task-1", title }),
);
withTodo.step((w) => {
  // @ts-expect-error a step's lines reach only the own service and the running peers of its Given
  w.client.as("client").send(devicePeer.requestNotificationPermission, {});
  // @ts-expect-error a step's own parameters keep their types
  addMilk(w, 1);
  return addMilk(w, "Buy milk");
});
scenarioOfScreens({
  description: "types",
  given: withTodo,
  when: (w) => ({ adding: addMilk(w, "Buy milk") }),
  then: ({ adding }) => [answered(adding, accepted())],
});
const rows: OutputOf<typeof tasks>["tasks"] = [{ taskId: "task-1", title: "Buy milk", dueAt: null, completedAt: null }];
const input: InputOf<typeof addTask> = { taskId: "task-1", title: "Buy milk" };
// @ts-expect-error an output has the fields of the query's output
const badRows: OutputOf<typeof tasks>["tasks"] = [{ taskId: "task-1" }];
void [rows, input, badRows];

// A line that may subscribe or not takes neither one answer nor a list, since answered wraps by what the line is.
const answerAny = (line: RequestLine<typeof addTask>) => [
  // @ts-expect-error a plain RequestLine may be a subscription
  answered(line, accepted()),
  // @ts-expect-error a plain RequestLine may be a single request
  answered(line, [accepted()]),
];
void answerAny;

// A shared condition reads the service's records, so it fits each guard and requires of the service.
const { condition, command: permissionCommand } = service({
  name: "permission",
  description: "",
  entities: {
    Permission: singleEntity({
      description: "",
      fields: { status: z.enum(["undetermined", "granted"]).default("undetermined") },
    }),
  },
});
const undetermined = condition(({ records }) => records.Permission.status === "undetermined");
permissionCommand({ callers: ["client"], emits: [], requires: { undetermined } }).decide(() => []);
// @ts-expect-error a condition compares an enum field only with its values
condition(({ records }) => records.Permission.status === "undeterminde");
