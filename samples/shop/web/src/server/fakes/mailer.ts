import type { Mail, Mailer } from "../orders/index.ts";

/** Stands in for the mail provider: keeps each mail and logs it. */
export class LoggingMailer implements Mailer {
  readonly sent: Mail[] = [];
  readonly #log: (line: string) => void;

  constructor(log: (line: string) => void = console.info) {
    this.#log = log;
  }

  async send(mail: Mail) {
    this.sent.push(mail);
    this.#log(`mail to ${mail.to}: ${mail.subject}`);
  }
}
