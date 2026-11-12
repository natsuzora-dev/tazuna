import { expect } from "@playwright/test";
import { pushedStream } from "../doubles/pushedStream.ts";
import { TaskListPage } from "../support/pages/TaskListPage.ts";
import { test } from "./fixtures.ts";

test("The list screen subscribes again when the subscription stream fails", async ({ page, held }) => {
  let subscribed = 0;
  held.whenHeld({
    tasks: (call) => {
      subscribed += 1;
      if (subscribed === 1)
        return call.answer(
          // biome-ignore lint/correctness/useYield: a stream that fails before its first value
          (async function* (): AsyncGenerator<{ tasks: [] }> {
            throw new Error("the database is gone");
          })(),
        );
      const { values, push } = pushedStream<{ tasks: [] }>(call.request);
      call.answer(values);
      push({ tasks: [] });
    },
    reminderSettings: (call) => call.answer(pushedStream<{ shouldRemind: boolean }>(call.request).values),
  });
  const list = new TaskListPage(page);
  await list.goto();
  await expect(list.emptyStatus).toBeVisible();
  expect(subscribed).toBe(2);
});
