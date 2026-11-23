import { instant } from "@natsuzora-dev/tazuna";
import { event } from "./data.ts";

/** `at` is when the user chose, which orders the choices, as they can arrive in any order. */
export const notificationPermissionGranted = event({ payload: { at: instant } });
export const notificationPermissionDenied = event({ payload: { at: instant } });
