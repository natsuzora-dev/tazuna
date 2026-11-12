import { EventPublisher } from "@orpc/server";
import type { device } from "@todo/spec/device";
import type { z } from "zod";

type Device = typeof device;
type CommandName = { [K in keyof Device]: Device[K] extends { readonly kind: "command" } ? K : never }[keyof Device];

type DeviceCall = {
  [K in CommandName]: { readonly name: K; readonly input: z.output<z.ZodObject<Device[K]["input"]>> };
}[CommandName];

export type DeviceRequest = DeviceCall & { readonly id: string };

export type DeviceResult = { readonly ok: true } | { readonly ok: false; readonly error: "unavailable" };

export const unavailable: DeviceResult = { ok: false, error: "unavailable" };

const requests = new EventPublisher<Record<string, DeviceRequest>>();
const pages: string[] = [];
const waiting = new Map<string, { readonly page: string; readonly answer: (answer: DeviceResult) => void }>();

export function sendToPage(request: DeviceCall): Promise<DeviceResult> {
  const page = pages.at(-1);
  if (page === undefined) return Promise.resolve(unavailable);
  const id = crypto.randomUUID();
  return new Promise((answer) => {
    waiting.set(id, { page, answer });
    requests.publish(page, { id, ...request });
  });
}

export async function* connectPage(signal: AbortSignal | undefined): AsyncGenerator<DeviceRequest> {
  const page = crypto.randomUUID();
  const received = requests.subscribe(page, { signal });
  pages.push(page);
  try {
    yield* received;
  } finally {
    pages.splice(pages.indexOf(page), 1);
    for (const [id, request] of waiting) if (request.page === page) answerRequest(id, unavailable);
  }
}

export function answerRequest(id: string, answer: DeviceResult): void {
  waiting.get(id)?.answer(answer);
  waiting.delete(id);
}
