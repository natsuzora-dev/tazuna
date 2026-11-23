import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Account = entity({
  description: "An account",
  fields: { id: z.string(), balance: z.int().min(-100).max(100) },
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

// withdraw breaks nonNegative, which deposit's proof of grew assumes.
export const withdraw = command({
  callers: ["client"],
  input: { accountId: ref(Account), amount: z.int().min(1).max(10) },
  emits: [balanceChanged],
  binds: { account: ({ input, records }) => records.Account.get(input.accountId) },
}).decide(({ input, bound }) => [
  emit(balanceChanged, { id: input.accountId, balance: bound.account.balance - input.amount }),
]);

export const deposit = command({
  callers: ["client"],
  input: { accountId: ref(Account), amount: z.int().min(1).max(10) },
  emits: [balanceChanged],
  binds: { account: ({ input, records }) => records.Account.get(input.accountId) },
  requires: { room: ({ bound }) => bound.account.balance <= 90 },
  ensures: { grew: ({ input, records }) => (records.Account.get(input.accountId)?.balance ?? 0) >= 1 },
}).decide(({ input, bound }) => [
  emit(balanceChanged, { id: input.accountId, balance: bound.account.balance + input.amount }),
]);

export const bankBounds = bounds({ creates: { Account: 1 } });
