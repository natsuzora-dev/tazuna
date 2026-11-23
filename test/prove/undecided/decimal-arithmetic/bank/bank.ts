import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Account = entity({
  description: "An account",
  fields: { id: z.string(), balance: z.number() },
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

export const openAccount = command({ input: { accountId: Account.fields.id }, emits: [accountOpened] }).decide(
  ({ input }) => [emit(accountOpened, { id: input.accountId, balance: 0 })],
);

export const deposit = command({
  input: { accountId: ref(Account), amount: z.number() },
  emits: [balanceChanged],
  binds: { account: ({ input, records }) => records.Account.get(input.accountId) },
}).decide(({ input, bound }) => [
  emit(balanceChanged, { id: input.accountId, balance: bound.account.balance + input.amount }),
]);

export const bankBounds = bounds({ creates: { Account: 2 } });
