import { expect, onTestFinished, test } from "vitest";
import { answerRequest, connectPage, sendToPage } from "../src/device/pages.server.ts";

const showNotification: Parameters<typeof sendToPage>[0] = {
  name: "showNotification",
  input: { notice: { id: "reminder", values: { title: "Buy milk" } } },
};

function connect() {
  const connection = new AbortController();
  const requests = connectPage(connection.signal);
  const disconnect = async () => {
    connection.abort();
    await requests.return(undefined);
  };
  onTestFinished(disconnect);
  return { received: requests.next(), requests, disconnect };
}

test("sendToPage answers unavailable when no page is connected", async () => {
  expect(await sendToPage(showNotification)).toEqual({ ok: false, error: "unavailable" });
});

test("sendToPage answers unavailable when the page disconnects before it answers", async () => {
  const page = connect();
  const answer = sendToPage(showNotification);
  await page.received;
  const next = page.requests.next();
  page.disconnect();
  await expect(next).rejects.toThrow();
  expect(await answer).toEqual({ ok: false, error: "unavailable" });
});

test("sendToPage sends the request to the last connected page and returns that page's answer", async () => {
  const first = connect();
  const last = connect();
  const answer = sendToPage(showNotification);
  const request = await last.received;
  if (request.done) throw new Error("the page was disconnected");
  answerRequest(request.value.id, { ok: true });
  expect(await answer).toEqual({ ok: true });
  expect(request.value).toEqual({ id: expect.any(String), ...showNotification });
  first.disconnect();
  await expect(first.received).rejects.toThrow();
});
