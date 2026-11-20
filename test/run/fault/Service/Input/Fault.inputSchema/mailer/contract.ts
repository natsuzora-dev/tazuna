import { contract, scheduleMail, sendMail } from "./mailer.ts";

export const mailer = contract({ scheduleMail, sendMail });
