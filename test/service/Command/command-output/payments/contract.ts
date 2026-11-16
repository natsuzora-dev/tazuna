import { contract } from "@natsuzora-dev/tazuna";
import { createCharge, refundCharge } from "./payments.ts";

export const payments = contract({ createCharge, refundCharge });
