import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const { automation, command, event, contract } = service({
  name: "notifier",
  description: "Take notifications, and ask the device for a permission on each",
});

export const notified = event({ payload: { text: z.string() } });

export const notify = command({ input: { text: z.string() }, emits: [notified] }).decide(({ input }) => [
  emit(notified, { text: input.text }),
]);

export const askOnNotified = automation({
  receives: { notified },
  commands: { requestPermission: device.requestPermission },
}).send({ onRejected: [] });
