import { expect, type Page } from "@playwright/test";
import { todo } from "@todo/spec/todo";
import type { z } from "zod";
import { timeZone } from "../../src/time.ts";
import type * as Held from "../doubles/held.ts";
import { keepOpen, pushedStream } from "../doubles/pushedStream.ts";
import { dueInputValue, TaskDetailPage } from "../support/pages/TaskDetailPage.ts";
import { test } from "./fixtures.ts";

const browserTime = Temporal.ZonedDateTime.from({ timeZone, year: 2026, month: 11, day: 2, hour: 10, minute: 10 });
const suggestion = browserTime.round({ smallestUnit: "hour", roundingMode: "floor" }).add({ hours: 1 });

const inputValue = (at: Temporal.ZonedDateTime) => dueInputValue(at.epochMilliseconds);

const shownDay = (at: Temporal.ZonedDateTime) => at.toLocaleString("en-US", { month: "short", day: "numeric" });

type TaskDetail = z.output<z.ZodObject<typeof todo.taskDetail.output>>;

async function openDetail(page: Page, held: typeof Held) {
  let task: NonNullable<TaskDetail["task"]> = {
    title: "Buy milk",
    isCompleted: false,
    dueAt: null,
    createdAt: browserTime.epochMilliseconds,
    remindAt: null,
  };
  const details = new Set<(detail: TaskDetail) => void>();
  let changeDueCount = 0;
  held.whenHeld({
    changeDue: (call) => {
      changeDueCount += 1;
      task = { ...task, dueAt: call.input.dueAt };
      call.answer();
      for (const push of details) push({ task });
    },
    taskDetail: (call) => {
      const { values, push } = pushedStream<TaskDetail>(call.request);
      call.answer(values);
      details.add(push);
      call.request.signal.addEventListener("abort", () => details.delete(push));
      push({ task });
    },
    tasks: keepOpen,
    reminderSettings: keepOpen,
    todoEvents: keepOpen,
  });
  await page.clock.setFixedTime(new Date(browserTime.epochMilliseconds));
  const detail = new TaskDetailPage(page);
  await detail.goto("task-1");
  await expect(detail.titleInput).toHaveValue(task.title);
  return { detail, changeDueCount: () => changeDueCount };
}

test("The due row of a task without a due date suggests the next full hour, and leaving the field makes it the due date", async ({
  page,
  held,
}) => {
  const { detail, changeDueCount } = await openDetail(page, held);

  await detail.toggleDue();
  await expect(detail.dueInput).toHaveValue(inputValue(suggestion));
  await expect(detail.clearDueButton).toBeHidden();
  await detail.dueInput.focus();
  await detail.titleInput.focus();
  await expect(detail.dueInput).toBeHidden();
  await expect(detail.dueRow).toContainText(shownDay(suggestion));
  await expect(detail.dueRow).toContainText(`${suggestion.hour}:00`);
  expect(changeDueCount()).toBe(1);

  await detail.toggleDue();
  await expect(detail.dueInput).toHaveValue(inputValue(suggestion));
  await detail.dueInput.press("Enter");
  await expect(detail.dueInput).toBeHidden();
  expect(changeDueCount()).toBe(1);
});

test("Pressing Enter in the date and time field makes its value the due date", async ({ page, held }) => {
  const { detail, changeDueCount } = await openDetail(page, held);
  const chosen = browserTime.toPlainDate().add({ days: 2 }).toZonedDateTime({ timeZone, plainTime: "09:00" });

  await detail.toggleDue();
  await detail.chooseDue(chosen.epochMilliseconds);
  await expect(detail.dueInput).toBeHidden();
  await expect(detail.dueRow).toContainText(shownDay(chosen));
  await expect(detail.dueRow).toContainText("9:00");
  expect(changeDueCount()).toBe(1);
});

test("Pressing the due row while editing the date and time field collapses the row without changing the due date", async ({
  page,
  held,
}) => {
  const { detail, changeDueCount } = await openDetail(page, held);

  await detail.toggleDue();
  await detail.dueInput.focus();
  await detail.dueInput.fill(inputValue(suggestion.add({ days: 3 })));
  await detail.toggleDue();
  await expect(detail.dueInput).toBeHidden();

  await detail.toggleDue();
  await expect(detail.dueInput).toHaveValue(inputValue(suggestion));
  await detail.dueInput.press("Enter");
  await expect(detail.dueRow).toContainText(shownDay(suggestion));
  expect(changeDueCount()).toBe(1);
});

test("The due row of a task with a due date shows that due date, and the clear button removes it", async ({
  page,
  held,
}) => {
  const { detail } = await openDetail(page, held);
  await detail.toggleDue();
  await detail.dueInput.press("Enter");
  await expect(detail.dueRow).toContainText(shownDay(suggestion));

  await detail.toggleDue();
  await expect(detail.dueInput).toHaveValue(inputValue(suggestion));
  await detail.clearDue();
  await expect(detail.dueInput).toBeHidden();
  await expect(detail.dueRow).toContainText("None");
});

test("Choosing a time after the limit keeps the due date and shows the latest time that can be chosen", async ({
  page,
  held,
}) => {
  const { detail, changeDueCount } = await openDetail(page, held);
  const until = browserTime.add({ milliseconds: todo.todoConstants.dueAheadLimit });

  await detail.toggleDue();
  await detail.chooseDue(until.add({ days: 1 }).epochMilliseconds);
  await expect(detail.dueError).toContainText(`${shownDay(until)}, ${until.year}`);
  await expect(detail.dueInput).toBeVisible();
  expect(changeDueCount()).toBe(0);
});
