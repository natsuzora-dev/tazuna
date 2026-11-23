import { contract, createCharge, refundCharge } from "./payments.ts";

export const payments = contract({ createCharge, refundCharge });
