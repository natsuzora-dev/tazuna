import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Account = entity({
  description: "An account",
  fields: { id: z.string(), balance: z.int() },
  key: "id",
  invariants: { nonNegative: ({ record }) => record.balance >= 0 },
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "bank",
  description: "Keep the balances",
  entities: { Account },
});

export const accountOpened = createEvent({ entity: Account });

export const balanceChanged = updateEvent({ entity: Account, writes: ["balance"] });

export const openAccount = command({
  callers: ["client"],
  input: { accountId: Account.fields.id },
  emits: [accountOpened],
}).decide(({ input }) => [emit(accountOpened, { id: input.accountId, balance: 0 })]);

export const withdraw = command({
  callers: ["client"],
  input: { accountId: ref(Account), amount: z.int().min(1) },
  emits: [balanceChanged],
  binds: { account: ({ input, records }) => records.Account.get(input.accountId) },
  requires: { covered: ({ input, bound }) => bound.account.balance >= input.amount },
}).decide(({ input, bound }) => [
  emit(balanceChanged, { id: input.accountId, balance: bound.account.balance - input.amount }),
]);

export const bankBounds = bounds({ creates: { Account: 2 } });
