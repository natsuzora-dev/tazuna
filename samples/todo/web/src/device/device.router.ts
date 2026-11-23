import { os } from "@orpc/server";
import { z } from "zod";
import { onNotificationPermission } from "../notifier/notifier.server.ts";
import { answerRequest, connectPage, unavailable } from "./pages.server.ts";

export const deviceRouter = {
  deviceRequests: os.handler(({ signal }) => connectPage(signal)),

  answerDeviceRequest: os
    .input(z.object({ id: z.string(), accepted: z.boolean() }))
    .handler(({ input }) => answerRequest(input.id, input.accepted ? { ok: true } : unavailable)),

  reportNotificationPermission: os
    .input(z.object({ granted: z.boolean(), at: z.int() }))
    .handler(({ input }) => onNotificationPermission(input)),
};
