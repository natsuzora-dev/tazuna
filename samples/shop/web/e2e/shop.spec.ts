import { expect, type Page, test } from "@playwright/test";

test.beforeEach(async ({ request }, testInfo) => {
  await request.post("/__test/reset", { data: { title: testInfo.title } });
});

test.afterEach(async ({ request }) => {
  await request.post("/__test/traces");
});

async function signIn(page: Page, role: "customer" | "staff") {
  await page.getByRole("button", { name: `Sign in as ${role}` }).click();
  await expect(page.getByText(`Signed in as ${role}`)).toBeVisible();
}

/** Staff price mugs at $12.00 and put `units` of them on the shelf. */
async function stockMugs(page: Page, units: number) {
  await page.goto("/staff");
  await signIn(page, "staff");
  const price = page.getByRole("form", { name: "Set price" });
  await price.getByLabel("SKU").fill("MUG");
  await price.getByLabel("Price").fill("12.00");
  await price.getByRole("button", { name: "Save price" }).click();
  await expect(price.getByRole("status")).toHaveText("MUG costs $12.00");
  const delivery = page.getByRole("form", { name: "Receive a delivery" });
  await delivery.getByLabel("SKU").fill("MUG");
  await delivery.getByLabel("Units").fill(String(units));
  await delivery.getByRole("button", { name: "Add to stock" }).click();
  await expect(delivery.getByRole("status")).toHaveText(`${units} MUG on hand`);
}

/** A customer orders mugs and lands on the order's page. Returns the order's id. */
async function orderMugs(page: Page, quantity: number) {
  await page.goto("/");
  await signIn(page, "customer");
  await page.getByLabel("Quantity of MUG").fill(String(quantity));
  await page.getByLabel("Email").fill("ann@example.com");
  await page.getByRole("button", { name: "Place order" }).click();
  await expect(page).toHaveURL(/\/orders\//);
  return page.url().split("/orders/")[1] ?? "";
}

const status = (page: Page) => page.getByRole("status");

async function paymentOf(page: Page, orderId: string) {
  await page.goto("/staff");
  await signIn(page, "staff");
  const lookup = page.getByRole("form", { name: "Find a payment" });
  await lookup.getByLabel("Order").fill(orderId);
  await lookup.getByRole("button", { name: "Find" }).click();
  return lookup.getByRole("status");
}

test("a paid order for the last units is confirmed", async ({ page }) => {
  await stockMugs(page, 2);
  const orderId = await orderMugs(page, 2);
  await expect(status(page)).toHaveText("Confirmed");
  await expect(await paymentOf(page, orderId)).toHaveText("$24.00: Captured");
  await page.goto("/");
  await expect(page.getByRole("row", { name: /MUG/ })).toContainText("0");
});

test("an incomplete order is refused with every reason", async ({ page }) => {
  await stockMugs(page, 2);
  await page.goto("/");
  await signIn(page, "customer");
  await page.getByRole("button", { name: "Place order" }).click();
  await expect(page.getByRole("alert")).toHaveText("Enter an email address. Add a product to the order");
});

test("an order for more than the stock is cancelled", async ({ page }) => {
  await stockMugs(page, 2);
  await orderMugs(page, 3);
  await expect(status(page)).toHaveText("Cancelled: a product is out of stock");
});

test("a declined payment cancels the order and puts the stock back", async ({ page, request }) => {
  await request.put("/__test/paygate", { data: { autoSettle: "decline" } });
  await stockMugs(page, 5);
  await orderMugs(page, 2);
  await expect(status(page)).toHaveText("Cancelled: the payment failed");
  await page.goto("/");
  await expect(page.getByRole("row", { name: /MUG/ })).toContainText("5");
});

test("an unpaid order is cancelled when its 15 minutes run out", async ({ page, request }) => {
  await request.put("/__test/paygate", { data: { autoSettle: null } });
  await stockMugs(page, 5);
  await orderMugs(page, 1);
  await expect(status(page)).toHaveText("Waiting for payment");
  await request.post("/__test/clock", { data: { advanceMs: 15 * 60_000 - 1 } });
  await page.reload();
  await expect(status(page)).toHaveText("Waiting for payment");
  await request.post("/__test/clock", { data: { advanceMs: 1 } });
  await expect(status(page)).toHaveText("Cancelled: it was not paid in time");
});

test("a payment the gateway takes after the customer cancels is refunded", async ({ page, request }) => {
  await request.put("/__test/paygate", { data: { autoSettle: null } });
  await stockMugs(page, 5);
  const orderId = await orderMugs(page, 1);
  await expect(status(page)).toHaveText("Waiting for payment");
  await page.getByRole("button", { name: "Cancel order" }).click();
  await expect(status(page)).toHaveText("Cancelled: you cancelled it");
  await request.post("/__test/paygate/settle", { data: { outcome: "approve" } });
  await expect(await paymentOf(page, orderId)).toHaveText("$12.00: Refunding");
  await request.post("/__test/paygate/settle", { data: { outcome: "approve" } });
  await page.getByRole("button", { name: "Find" }).click();
  await expect(page.getByRole("form", { name: "Find a payment" }).getByRole("status")).toHaveText("$12.00: Refunded");
});
