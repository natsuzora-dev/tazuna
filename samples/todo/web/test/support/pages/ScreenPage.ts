import type { Locator, Page } from "@playwright/test";

export abstract class ScreenPage {
  readonly page: Page;
  readonly region: Locator;

  constructor(page: Page, region: string) {
    this.page = page;
    this.region = page.getByRole("region", { name: region, exact: true });
  }
}
