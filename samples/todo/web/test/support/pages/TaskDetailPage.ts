import { expect, type Locator, type Page } from "@playwright/test";
import { zoned } from "../../../src/time.ts";
import { ScreenPage } from "./ScreenPage.ts";

export const dueInputValue = (at: number) => zoned(at).toPlainDateTime().toString({ smallestUnit: "minute" });

export class TaskDetailPage extends ScreenPage {
  readonly closeLink: Locator;
  readonly completeButton: Locator;
  readonly reopenButton: Locator;
  readonly titleInput: Locator;
  readonly dueRow: Locator;
  readonly dueInput: Locator;
  readonly clearDueButton: Locator;
  readonly deleteButton: Locator;
  readonly dueError: Locator;

  constructor(page: Page) {
    super(page, "Task details");
    this.closeLink = this.region.getByTestId("close");
    this.completeButton = this.region.getByTestId("complete");
    this.reopenButton = this.region.getByTestId("reopen");
    this.titleInput = this.region.getByTestId("rename");
    this.dueRow = this.region.getByTestId("dueToggle");
    this.dueInput = this.region.getByTestId("dueChoose");
    this.clearDueButton = this.region.getByTestId("dueClear");
    this.deleteButton = this.region.getByTestId("delete");
    this.dueError = this.region.getByRole("alert");
  }

  async goto(taskId: string) {
    await this.page.goto(`/tasks/${taskId}`);
  }

  async expectTask(task: { readonly title: string; readonly isCompleted: boolean } | null) {
    if (task === null) return expect(this.completeButton).toBeDisabled();
    await expect(this.titleInput).toHaveValue(task.title);
    await expect(task.isCompleted ? this.reopenButton : this.completeButton).toBeVisible();
  }

  async close() {
    await this.closeLink.click();
  }

  async complete() {
    await this.completeButton.click();
  }

  async reopen() {
    await this.reopenButton.click();
  }

  async rename(title: string) {
    await this.titleInput.fill(title);
    await this.titleInput.press("Enter");
  }

  async toggleDue() {
    await this.dueRow.click();
  }

  async chooseDue(dueAt: number) {
    await this.dueInput.fill(dueInputValue(dueAt));
    await this.dueInput.press("Enter");
  }

  async clearDue() {
    await this.clearDueButton.click();
  }

  async delete() {
    await this.deleteButton.click();
  }
}
