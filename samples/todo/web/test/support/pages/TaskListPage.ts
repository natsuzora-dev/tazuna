import { expect, type Locator, type Page } from "@playwright/test";
import type { Filter } from "../../../src/todo/queries.server.ts";
import { ScreenPage } from "./ScreenPage.ts";

const filterLabels = { open: "Open", completed: "Completed", all: "All" } satisfies Record<Filter, string>;

export class TaskListPage extends ScreenPage {
  readonly titleInput: Locator;
  readonly filters: Locator;
  readonly remindersSwitch: Locator;
  readonly emptyStatus: Locator;
  readonly rows: Locator;

  constructor(page: Page) {
    super(page, "Task list");
    this.titleInput = this.region.getByTestId("add");
    this.filters = this.region.getByTestId("filter");
    this.remindersSwitch = this.region.getByTestId("remindersToggle");
    this.emptyStatus = this.region.getByText("No tasks");
    this.rows = this.region.getByRole("listitem");
  }

  async goto() {
    await this.page.goto("/");
  }

  filterOption(filter: Filter): Locator {
    return this.filters.getByRole("radio", { name: filterLabels[filter], exact: true });
  }

  taskLink(title: string): Locator {
    return this.region.locator(this.link(title));
  }

  completeButton(title: string): Locator {
    return this.row(title).getByTestId("complete");
  }

  reopenButton(title: string): Locator {
    return this.row(title).getByTestId("reopen");
  }

  async add(title: string) {
    await this.titleInput.fill(title);
    await this.titleInput.press("Enter");
  }

  async filter(filter: Filter) {
    await this.filterOption(filter).check();
  }

  async openTask(title: string) {
    await this.taskLink(title).click();
  }

  async complete(title: string) {
    await this.completeButton(title).click();
  }

  async reopen(title: string) {
    await this.reopenButton(title).click();
  }

  async toggleReminders(on: boolean) {
    await expect(this.remindersSwitch).toBeChecked({ checked: !on });
    await this.remindersSwitch.click();
  }

  async expectTasks(tasks: readonly { readonly title: string; readonly isCompleted: boolean }[]) {
    if (tasks.length === 0) return expect(this.emptyStatus).toBeVisible();
    await expect(this.rows).toHaveCount(tasks.length);
    for (const { title, isCompleted } of tasks)
      await expect(isCompleted ? this.reopenButton(title) : this.completeButton(title)).toBeVisible();
  }

  async expectReminders(shouldRemind: boolean) {
    await expect(this.remindersSwitch).toBeChecked({ checked: shouldRemind });
  }

  private row(title: string): Locator {
    return this.rows.filter({ has: this.link(title) });
  }

  private link(title: string): Locator {
    return this.page.getByTestId("openTask").and(this.page.getByRole("link", { name: title, exact: true }));
  }
}
