# The todo sample

This sample takes one small spec through every tazuna command, then compares an implementation's log with it.
`spec/` holds the spec, a Gleam project.
`web/` holds an implementation of the same service and a script that records its log.

The service keeps a list of at most two open tasks.
A user adds a task with `add` and completes it with `complete`, which removes it.
The query `open tasks` answers how many tasks are open.
An hour after a task is added, if it is still open, the `reminder` machine runs the service's own command `remind`, and the `mail` reaction asks the external `mailer` to send a reminder.

The sample is user documentation.
tazuna's own tests never read it.

## Before you start

You need Gleam, Erlang/OTP, and Node for the harness in `web/`.
On its first run the launcher fetches the engine and z3 for its version.
To use an engine you built from this repository instead, set `TAZUNA_ENGINE` to its path, such as `lean/.lake/build/bin/tazuna-engine`, and put z3 on `PATH`.

Run every command below from `spec/`.

## Check the spec

```sh
gleam run -m tazuna -- check todo_spec
```

`check` converts `src/todo_spec.gleam` and checks the structure of the spec:

```json
{"kind":"Check.passed","service":"todo"}
```

## Prove what holds

```sh
gleam run -m tazuna -- prove todo_spec
```

`prove` checks the spec in the model that `model()` returns, beside `spec()`.
`spec()` says what the service means; the model says how far `prove` and `generate` look: at most two open tasks, two items in every other collection, and runs of up to three inputs.
A root module can define more models, such as a larger one for a nightly run, and `--model <name>` picks one.

`prove` prints one line per target and input kind.
The targets here are the invariant `every title is not empty`, the reminder's invariant `a due reminder went out`, each `ensures` rule, the `cascade` bound, the effect `remind`, the order of two `remind` effects, the reminder's timers, and the response.
The first line says that the initial records keep the invariant:

```json
{"assumes":[],"kind":"Prove.proved","service":"todo","step":"init","target":"invariant every title is not empty"}
```

The other 30 lines read `Prove.withinBounds`, and the command exits 0.
No step breaks its target while the state fits the model's slots, but a step can grow the task table past the two tasks that `creates` allows.
Each line's `scope` names the model and lists those bounds.

The response `an added task is reminded or done within an hour` reads `Prove.withinBounds` as well, at each input kind.
Its `deadline` reads a task's `remind_at` until the reminder goes out, which `apply` writes down as `reminded`; `prove` checks each step against it, so the line holds for runs of any length within the slots.

## Test the scenario

```sh
gleam run -m tazuna -- test todo_spec --update
gleam run -m tazuna -- test todo_spec
```

The scenario `remind the open task` adds a task with an empty title to show an invalid answer, adds two tasks, completes one, asks `open tasks`, waits an hour, and answers the mailer.
`test --update` writes its trace to `snapshots/todo/remind the open task.jsonl`.
Later runs compare the trace with that snapshot:

```json
{"kind":"Test.passed","scenario":"remind the open task","service":"todo"}
```

In the snapshot, `open tasks` answers `1` after the completion.
After the clock line at 3600000 it shows one `ReminderDue` event and one request to `mailer`, for the task that is still open.

## Generate inputs for an implementation

```sh
gleam run -m tazuna -- generate todo_spec inputs
```

`generate` writes one trace to `inputs/todo/` for each class of output it reaches, such as `add accepted` or `request mailer.send`:

```json
{"file":"todo/add accepted.jsonl","kind":"Generate.reached","service":"todo","steps":1,"target":"add accepted"}
```

Every target is reached.
`add` rejects with `TooManyOpenTasks` once two tasks are open.
Tasks added at one time come due at one time, and each due reminder takes one internal step of the clock line that reaches it, so the cap is what keeps a clock line within the service's `cascade` of 2.
The model's `others_at_most` of 2 lets the reminder's two instances fit, so `generate` reaches the rejection too.

`remind` lists only `tazuna.Own` in `callers`, so only the service itself runs it, through the `reminder` machine.
Its one target, `remind invalid callers`, is an outside request that the implementation must refuse.

## Explore the states

```sh
gleam run -m tazuna -- explore todo_spec found
```

`explore` searches the states the service reaches from its initial state breadth first, as TLC does, trying every input from each state.
`add` takes the titles the model's `values` list, `""` and `"Buy milk"`; every id field takes the ids the state holds and one new one.
A clock line moves time by the model's wait of an hour, and to each deadline the state holds and the millisecond after it.
The search stops at `explore_depth`, six inputs:

```json
{"kind":"Explore.covered","scope":{"capped":false,"depth":6,"exhausted":false,"exploreDepth":6,"exploreStates":10000,"model":"model","othersAtMost":2,"values":[{"input":"command add","ints":[],"strings":["","Buy milk"]}],"waits":[3600000]},"service":"todo","states":[1,1,3,10,21,37,58],"transitions":845}
```

It reaches every target `generate` reaches and writes its runs to `found/todo/`.
The seven targets a fault or a late answer breaks read `Explore.notViolated` for runs of up to six inputs.
Without the cap on open tasks, the `cascade bound` line reads `Explore.violated` instead: three tasks added at one time come due at one clock line, and their three reminders take more internal steps than the `cascade` of 2 allows.
`prove` reads that bound `Prove.withinBounds`, as it looks at two tasks only.

## Verify an implementation's log

`web/todo.mjs` is the service as an implementation writes it, with its own names for tasks (`task-1`) and mail requests (`mail-1`).
`web/replay.mjs` reads the `in` lines of each trace in a directory, feeds them to the implementation, and writes the implementation's own trace.

1. Replay the generated inputs and the snapshot:

   ```sh
   node ../web/replay.mjs inputs/todo traces
   node ../web/replay.mjs snapshots/todo traces
   ```

2. Compare the traces with the spec:

   ```sh
   gleam run -m tazuna -- verify todo_spec traces
   ```

   Every trace passes:

   ```json
   {"kind":"Verify.passed","trace":"traces/remind the open task.jsonl"}
   ```

The trace keeps the implementation's names, as [Traces](../../docs/concepts.md#traces) allows.
The replay script maps names the other way, because a generated input refers to tasks and requests by the spec's names.

To see a failure, change `state.dueAt <= now` to `state.dueAt < now` in `web/todo.mjs`, which fires the reminder only after its deadline, and run both steps again.
Two traces fail, because their clock line reaches the deadline exactly:

```json
{"actual":[],"expected":["{\"out\":\"event\",\"time\":3600000,\"value\":{\"tag\":\"ReminderDue\",\"task\":\"task-2\",\"title\":\"Call the bank\"}}","{\"external\":\"mailer\",\"id\":\"?0\",\"input\":{\"subject\":\"Call the bank\",\"tag\":\"Mail\"},\"name\":\"send\",\"out\":\"request\",\"time\":3600000}"],"kind":"Verify.differs","line":15,"trace":"traces/remind the open task.jsonl"}
```

## Read a line you do not know

```sh
gleam run -m tazuna -- explain Prove.withinBounds
```

`explain` prints what a kind of line means, its exit code, its fields, and the theorems behind it.
Run it with no kind to list every kind.
