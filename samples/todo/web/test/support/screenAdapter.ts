import type { AnyCommand, AnyQuery, CommandAnswer } from "@natsuzora-dev/tazuna";
import { expect, type Locator, type Page, type Request } from "@playwright/test";
import { todo } from "@todo/spec/todo";
import { z } from "zod";
import { taskDetailScreen } from "../../../spec/screens/taskDetailScreen.ts";
import { taskListScreen } from "../../../spec/screens/taskListScreen.ts";
import type { TodoEvent } from "../../src/todo/events.server.ts";
import type * as Held from "../doubles/held.ts";
import { pushedStream } from "../doubles/pushedStream.ts";
import { commandRequest, type OutputSlot, queryRequest, type ReplayAdapter } from "../harness/replay.ts";
import { toApp } from "./answers.ts";
import { TaskDetailPage } from "./pages/TaskDetailPage.ts";
import { TaskListPage } from "./pages/TaskListPage.ts";

interface Operation {
  readonly control: Locator;
  readonly perform: () => Promise<void>;
}

const on = (control: Locator, perform: () => Promise<void>): Operation => ({ control, perform });

type OperationsOf<S extends string, C> = {
  readonly [K in keyof C & string as `${S}.${K}`]: (payload: unknown) => Operation | undefined;
};

type Operations = OperationsOf<"taskListScreen", typeof taskListScreen.controls> &
  OperationsOf<"taskDetailScreen", typeof taskDetailScreen.controls>;

function payloadOf<P extends z.ZodRawShape>(control: { readonly payload?: P }, payload: unknown) {
  if (control.payload === undefined) throw new Error("the control has no payload");
  return z.object(control.payload).parse(payload);
}

const { controls: onList } = taskListScreen;
const { controls: onDetail } = taskDetailScreen;

function operationsOn(
  list: TaskListPage,
  detail: TaskDetailPage,
  titleOf: (taskId: string) => string | undefined,
): Operations {
  const onTask = (taskId: string, operation: (title: string) => Operation) => {
    const title = titleOf(taskId);
    return title === undefined ? undefined : operation(title);
  };
  return {
    "taskListScreen.filter": (payload) => {
      const { filter } = payloadOf(onList.filter, payload);
      return on(list.filterOption(filter), () => list.filter(filter));
    },
    "taskListScreen.openTask": (payload) => {
      const { title } = payloadOf(onList.openTask, payload);
      return on(list.taskLink(title), () => list.openTask(title));
    },
    "taskListScreen.add": (payload) => on(list.titleInput, () => list.add(payloadOf(onList.add, payload).title)),
    "taskListScreen.complete": (payload) =>
      onTask(payloadOf(onList.complete, payload).taskId, (title) =>
        on(list.completeButton(title), () => list.complete(title)),
      ),
    "taskListScreen.reopen": (payload) =>
      onTask(payloadOf(onList.reopen, payload).taskId, (title) =>
        on(list.reopenButton(title), () => list.reopen(title)),
      ),
    "taskListScreen.remindersToggle": (payload) =>
      on(list.remindersSwitch, () => list.toggleReminders(payloadOf(onList.remindersToggle, payload).shouldRemind)),
    "taskDetailScreen.close": () => on(detail.closeLink, () => detail.close()),
    "taskDetailScreen.complete": () => on(detail.completeButton, () => detail.complete()),
    "taskDetailScreen.reopen": () => on(detail.reopenButton, () => detail.reopen()),
    "taskDetailScreen.rename": (payload) =>
      on(detail.titleInput, () => detail.rename(payloadOf(onDetail.rename, payload).title)),
    "taskDetailScreen.dueToggle": () => on(detail.dueRow, () => detail.toggleDue()),
    "taskDetailScreen.dueChoose": (payload) =>
      on(detail.dueInput, () => detail.chooseDue(payloadOf(onDetail.dueChoose, payload).dueAt)),
    "taskDetailScreen.dueClear": () => on(detail.clearDueButton, () => detail.clearDue()),
    "taskDetailScreen.delete": () => on(detail.deleteButton, () => detail.delete()),
  };
}

interface Call {
  readonly request: globalThis.Request;
}

interface Sent {
  readonly request: Request;
  readonly slotAtRequest: OutputSlot;
  call?: Call;
  subscription?: string | undefined;
  slotAtFailure?: OutputSlot;
}

interface Unbound {
  readonly call: Call;
  readonly write: (output: OutputSlot) => string | undefined;
}

const isSentAs = (call: Call) => (sent: Sent) =>
  sent.call === undefined &&
  sent.request.method() === call.request.method &&
  sent.request.url() === call.request.url &&
  sent.request.headers()["idempotency-key"] === (call.request.headers.get("idempotency-key") ?? undefined);

/**
 * Requests on separate connections may reach the server out of order, so output lines follow the order of Playwright's
 * request and requestfailed events.
 */
export function screenAdapter(page: Page, held: typeof Held): ReplayAdapter & { readonly unboundCalls: () => Call[] } {
  const list = new TaskListPage(page);
  const detail = new TaskDetailPage(page);
  const busy = page.locator('[aria-busy="true"]');
  const titles = new Map<string, string>();
  const operations = new Map(Object.entries(operationsOn(list, detail, (id) => titles.get(id))));
  const operationOf = (name: string, payload: unknown) => {
    const operation = operations.get(name);
    if (operation === undefined) throw new Error(`the screen adapter has no operation ${name}`);
    return operation(payload);
  };
  let unansweredCommands = 0;
  const unshownAnswers = new Map<AnyQuery, () => Promise<void>>();
  let time: Temporal.Instant;
  const sent: Sent[] = [];
  const unbound: Unbound[] = [];
  const eventStreams = new Set<(event: TodoEvent) => void>();

  const unsubscribe = (entry: Sent) => {
    if (entry.subscription !== undefined) entry.slotAtFailure?.unsubscribe(entry.subscription);
  };
  const bind = () => {
    for (const waiting of unbound.splice(0)) {
      const entry = sent.find(isSentAs(waiting.call));
      if (entry === undefined) {
        unbound.push(waiting);
        continue;
      }
      entry.call = waiting.call;
      entry.subscription = waiting.write(entry.slotAtRequest);
      unsubscribe(entry);
    }
  };
  const receive = (waiting: Unbound) => {
    unbound.push(waiting);
    bind();
  };
  const command =
    (definition: AnyCommand) =>
    (call: Call & { readonly input: unknown; readonly answer: () => void; readonly fail: (error: Error) => void }) => {
      const id = call.request.headers.get("idempotency-key");
      if (id === null) throw new Error("the command has no Idempotency-Key");
      unansweredCommands += 1;
      const answer = (a: CommandAnswer) => {
        unansweredCommands -= 1;
        const error = toApp.commandError(a);
        if (error === undefined) call.answer();
        else call.fail(error);
      };
      receive({
        call,
        write: (output) => {
          output.request({ ...commandRequest(definition, call.input, answer), id });
          return undefined;
        },
      });
    };
  const subscription =
    <Q extends AnyQuery>(
      definition: Q,
      expectShown: (output: z.output<z.ZodObject<Q["output"]>>) => () => Promise<void>,
    ) =>
    (
      call: Call & {
        readonly input: unknown;
        readonly answer: (values: AsyncGenerator<z.output<z.ZodObject<Q["output"]>>>) => void;
      },
    ) => {
      const { values, push } = pushedStream<z.output<z.ZodObject<Q["output"]>>>(call.request);
      call.answer(values);
      receive({
        call,
        write: (output) =>
          output.subscribe(
            queryRequest(definition, call.input, (answer) => {
              if (answer.result !== "fulfilled") throw new Error("the subscriptions of todo answer only fulfilled");
              unshownAnswers.set(definition, expectShown(answer.output));
              push(answer.output);
            }),
          ),
      });
    };

  return {
    async start(outputs, startTime) {
      time = startTime;
      page.on("request", (request) => {
        sent.push({ request, slotAtRequest: outputs.later() });
        bind();
      });
      page.on("requestfailed", (request) => {
        const entry = sent.find((s) => s.request === request);
        if (entry === undefined) return;
        entry.slotAtFailure = outputs.later();
        unsubscribe(entry);
      });
      held.whenHeld({
        addTask: command(todo.addTask),
        completeTask: command(todo.completeTask),
        reopenTask: command(todo.reopenTask),
        renameTask: command(todo.renameTask),
        deleteTask: command(todo.deleteTask),
        changeDue: command(todo.changeDue),
        changeReminders: command(todo.changeReminders),
        tasks: subscription(todo.tasks, (output) => {
          for (const task of output.tasks) titles.set(task.taskId, task.title);
          const shown = output.tasks.map((t) => ({ title: t.title, isCompleted: t.completedAt !== null }));
          return async () => {
            if (await list.region.isVisible()) await list.expectTasks(shown);
          };
        }),
        taskDetail: subscription(todo.taskDetail, (output) => async () => {
          if (await detail.region.isVisible()) await detail.expectTask(output.task);
        }),
        reminderSettings: subscription(todo.reminderSettings, (output) => async () => {
          if (await list.region.isVisible()) await list.expectReminders(output.shouldRemind);
        }),
        todoEvents: (call) => {
          const { values, push } = pushedStream<TodoEvent>(call.request);
          call.answer(values);
          eventStreams.add(push);
          call.request.signal.addEventListener("abort", () => eventStreams.delete(push));
          receive({ call, write: () => undefined });
        },
      });
      await page.clock.setFixedTime(time.epochMilliseconds);
      await list.goto();
    },
    now: () => time,
    async advanceTo(to) {
      if (to.equals(time)) return;
      time = to;
      await page.clock.setFixedTime(time.epochMilliseconds);
    },
    async untilQuiet(outputs) {
      // The browser does not signal when a request from a React effect is sent, so wait until the request and output
      // counts hold still for a poll interval.
      let before = "";
      await expect
        .poll(
          async () => {
            const now = `${sent.length} ${outputs()}`;
            const isUnchanged = now === before;
            before = now;
            const isBusy = (await busy.count()) > 0;
            return isUnchanged && unbound.length === 0 && isBusy === unansweredCommands > 0;
          },
          { intervals: [100] },
        )
        .toBe(true);
      for (const expectShown of unshownAnswers.values()) await expectShown();
      unshownAnswers.clear();
    },
    async operate({ name, payload }) {
      const operation = operationOf(name, payload);
      if (operation === undefined) throw new Error(`${name} names a task that the screen does not show`);
      await expect(operation.control).toBeVisible();
      await expect(operation.control).toBeEnabled();
      await operation.perform();
    },
    async cannotOperate({ name, payload }) {
      const operation = operationOf(name, payload);
      if (operation === undefined) return;
      const enabled = page.locator(':not(:disabled):not([aria-disabled="true"])');
      await expect(operation.control.filter({ visible: true }).and(enabled)).toHaveCount(0);
    },
    receive(event) {
      for (const push of eventStreams) push(toApp.todoEvent(event));
    },
    unboundCalls: () => unbound.map((waiting) => waiting.call),
  };
}
