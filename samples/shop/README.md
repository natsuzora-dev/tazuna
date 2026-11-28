# The shop sample

This sample is a small online shop, sized like a system a team would really specify: three services that talk through events, two outside systems, a deadline, and money.
It takes the spec through every tazuna command and shows what each stage found while the spec was written.
`spec/` holds the spec, a Gleam project.
`web/` holds an implementation of the shop as a team would build it today, and `verify` compares its logs with the spec.

The sample is user documentation.
tazuna's own tests never read it.
Start with the [todo sample](../todo/README.md) if you have not used tazuna before; this page assumes you know its commands.

## How the shop works

Orders runs the checkout.
It asks the other services for what it needs by publishing events, and it moves an order on when their events come back:

1. A customer places an order for one or more lines, such as two units of the product `MUG`. Orders prices each line from its price list, and publishes `OrderPlaced`.
2. Inventory holds the stock for every line of the order, or for none of them, and publishes `StockHeld` or `OutOfStock`.
3. Once the stock is held, orders publishes `PaymentDue` with the total.
4. Payments charges the total at the payment gateway, and publishes `PaymentCaptured` or `PaymentFailed`.
5. Orders confirms a paid order, and mails the customer.

An order that is not paid within 15 minutes of being placed is cancelled.
So is an order whose stock is short or whose payment fails, and the customer may cancel an order that is still open.
When an order is cancelled, inventory puts its stock back on the shelf, and payments refunds the charge if the gateway took the money.
The gateway may take the money after the order was cancelled, so payments refunds a late charge too.

Each service is one module in `spec/src/shop_spec/`, and `shared.gleam` holds the types they share:

- `orders.gleam` keeps the orders and the price list. Staff run `set price`, and customers run `place order`, `cancel order`, and the query `order status`. The machine `payment deadline` has one instance per open order and cancels the order when its time to pay runs out. The reaction `checkout` turns the news from inventory and payments into the service's own commands, `request payment`, `confirm`, and `cancel for`, and asks the external `mailer` to mail the customer. At most three orders wait for stock or payment at a time.
- `inventory.gleam` keeps the units on the shelf per product and the lines held for each open order. Staff run `restock`. The reaction `holding` runs the own command `hold` for each order placed.
- `payments.gleam` keeps one payment per order. The reaction `gateway` runs the own command `take` for each payment due, sends the charge to the external `payment gateway`, and runs `give back` to refund a cancelled order's charge.

`spec/src/shop_spec.gleam` lists the services and the externals in `spec()`.
`model()` beside it holds the scope that `prove`, `explore`, and `search` check them in.

## Before you start

You need Gleam and Erlang/OTP, and Node 24 or later for the implementation in `web/`.
On its first run the launcher fetches the engine and z3 for its version.
To use an engine you built from this repository instead, set `TAZUNA_ENGINE` to its path, such as `lean/.lake/build/bin/tazuna-engine`, and put z3 on `PATH`.

Run every command below from `spec/`.
The times are from one run on an Apple M2 laptop with `--jobs 4` and an empty cache.

## Check the spec

```sh
gleam run -m tazuna -- check shop_spec
```

`check` converts the modules and checks the structure of each service:

```json
{"kind":"Check.passed","service":"orders"}
{"kind":"Check.passed","service":"inventory"}
{"kind":"Check.passed","service":"payments"}
```

The first draft of `model()` named a bound only for the orders table, and `check` printed one `Illegal.creates` line for each of the other four tables, such as `inventory: the table stock needs a create bound`.
Every table in a service's records needs a bound in the model, because `prove` checks states with that many entries and no more.
Each module's `scope()` now names them all.

## Prove what holds

```sh
gleam run -m tazuna -- prove shop_spec --jobs 4
```

`prove` checks each invariant, each `ensures` rule, the response, the `cascade` bound, and each own command, one input at a time.
It starts from any state where the invariants hold, not only from states a run reaches, and asks the solver whether one input can break the target.
It asks 287 questions and takes about 12 seconds.

The six invariants hold in the initial state:

```json
{"assumes":[],"kind":"Prove.proved","service":"payments","step":"init","target":"invariant no cancelled order keeps its money"}
```

171 lines read `Prove.withinBounds`: no input breaks the target in any state that fits the model, such as three orders and two prices in orders.
Each line's `scope` lists those bounds.

### What prove found

`prove` found a real bug in inventory.
`hold` took the quantities in `OrderPlaced` on trust.
A hold for a quantity of -22775 adds stock instead of taking it, another order can then hold that stock, and cancelling the first order takes stock below zero:

```
holds: order ~35 holds -22775 units, stock 3275
input: OrderCancelled for order ~35
outcome: fault invariant no stock level is negative
```

Orders never sends such a quantity, but inventory must not depend on that: an event from another service is an input like any other.
`hold` now rejects an order with a quantity that is not positive.

Two counterexamples showed states that no run reaches, and each led to one more invariant:

- After the fix, the same cancellation broke the invariant from a state that held a negative quantity. `hold` no longer makes such a hold, but `prove` did not know that, because it checks every state where the invariants hold. The invariant `every held quantity is positive` says so, and `prove` now uses it.
- In orders, a clock line broke the response from a state where the `payment deadline` of an open order had already passed. That state cannot happen: a deadline that passes cancels its order in the same step. The machine invariant `a passed deadline has cancelled its order` says so.

This is the usual way to work with `prove`.
A counterexample from a state no run reaches tells you which fact the spec relies on but does not state.

### Pairs of own commands

Some lines are pairs of own commands, such as `own command take and own command take commute`.
If one step queued both, the result would depend on which runs first.

`prove` reads off the code which pairs a step can queue, and with which inputs:

- An event line applies one event, so each reaction runs once on it and takes one clause of its `case`. Each clause sends at most one own command, so no step queues two `take` commands, or `request payment` with the `cancel for` of `OutOfStock`, and `prove` does not ask whether such pairs commute.
- When two payment deadlines pass at once, one clock line queues two `cancel for` commands. The deadline always sends the reason `NotPaidInTime`, so `prove` asks whether two such commands commute only with that reason, and they do.

So every pair line reads `Prove.withinBounds`, and `prove` exits 0.

## Test the scenarios

```sh
gleam run -m tazuna -- test shop_spec --update
gleam run -m tazuna -- test shop_spec
```

Orders has two scenarios:

- `a paid order is confirmed` sets the price of `MUG`, orders two mugs, receives `StockHeld` and `PaymentCaptured`, asks for the order's status, and answers the mail.
- `an unpaid order is cancelled` receives `StockHeld` but no payment. The status reads `AwaitingPayment` after 14 minutes, and after 15 minutes the order is cancelled with the reason `NotPaidInTime` and the mail goes out.

`test --update` writes their traces to `snapshots/orders/`, and later runs compare with them:

```json
{"kind":"Test.passed","scenario":"an unpaid order is cancelled","service":"orders"}
```

Inventory and payments have no scenarios, because their orders come from outside the service, and a scenario cannot yet name an id that the service did not make.

## Write inputs for an implementation

```sh
gleam run -m tazuna -- search shop_spec inputs --jobs 4
```

`search` runs `prove`, then `explore`, then its own stage.
It takes about 25 seconds, and `explore` takes about 11 of them.

`explore` runs the service from its initial state, tries every input from each state it reaches, and keeps going for six inputs.
For a field that holds a number or a string, it tries the values `model()` lists for that input.
They are the values on both sides of each limit the spec names, and `""` for a string that must not be empty.
For `place order`, that is the quantities 0, 1, 10, and 11, around the rule `each quantity is 1 to 10`, and the strings `""` and `MUG`:

| Service | States per depth | Transitions | Note |
| --- | --- | --- | --- |
| orders | 1, 1, 5, 55, 455, 3555, 5928 | 1,071,256 | stops at its cap of 10,000 states |
| inventory | 1, 2, 4, 10, 21, 44, 93 | 6,108 | |
| payments | 1, 1, 5, 12, 40, 112, 353 | 8,993 | |

`explore` reaches all 51 classes of output, such as `place order rejected TooManyCheckouts` or `request payment gateway.refund`, and writes one trace for each to `inputs/`.
For example, `inputs/payments/event RefundDone.jsonl` charges an order, receives its cancellation after the gateway took the money, and refunds it.

The 18 targets that a fault or a late answer breaks read `Explore.notViolated`: no run of up to six inputs breaks them.
They include `no cancelled order keeps its money`, whichever comes first of the cancellation and the gateway's answer, and the response that a placed order is confirmed or cancelled within 15 minutes.

`search`'s own stage asks the solver for runs that reach what `explore` did not.
Here nothing is left for it, so it prints no `Search` line.

## Verify an implementation

`web/` is a React app and a Node server that runs the three services, each with its own database, and passes events between them through outboxes.
[Its README](web/README.md) describes the app and `web/tazuna/`, the only code in it that knows the spec.
Run these from `web/`:

```sh
npm run verify
npm run e2e
npm run verify:e2e
```

`npm run verify` feeds the `in` lines of each trace in `spec/inputs/` and `spec/snapshots/` to the service the trace names, records what the service does, and runs `verify` on the 53 recorded traces.
`npm run e2e` runs six Playwright tests through the browser, and records one trace per service for each test; `npm run verify:e2e` runs `verify` on those 17 traces.
Every trace passes:

```json
{"kind":"Verify.passed","trace":"../web/traces/inputs/payments/event RefundDone.jsonl"}
```

The two sets of traces check different runs.
`search` writes one run for each class of output, the shortest it finds, so `inputs/payments/event RefundDone.jsonl` refunds a charge that the gateway took before the order was cancelled.
To see what that leaves out, delete the refund from the `charge.succeeded` case in `web/src/server/payments/payments.ts`, so a charge taken after the cancellation is kept.
All 53 replayed traces still pass.
The trace of the end-to-end test `a payment the gateway takes after the customer cancels is refunded` fails, because the spec refunds that charge in the same step:

```json
{"actual":["{\"out\":\"event\",\"time\":0,\"value\":{\"order\":\"2873b2f9-53f2-4840-abf3-d4c35d03162c\",\"tag\":\"ChargeCaptured\",\"transaction\":\"txn_1\"}}"],"expected":["{\"out\":\"event\",\"time\":0,\"value\":{\"order\":\"2873b2f9-53f2-4840-abf3-d4c35d03162c\",\"tag\":\"ChargeCaptured\",\"transaction\":\"txn_1\"}}","{\"out\":\"event\",\"time\":0,\"value\":{\"order\":\"2873b2f9-53f2-4840-abf3-d4c35d03162c\",\"tag\":\"RefundStarted\",\"transaction\":\"txn_1\"}}","{\"external\":\"payment gateway\",\"id\":\"?1\",\"input\":{\"amount\":1200,\"tag\":\"Refund\",\"transaction\":\"txn_1\"},\"name\":\"refund\",\"out\":\"request\",\"time\":0}"],"kind":"Verify.differs","line":8,"trace":"../web/e2e-traces/payments/a payment the gateway takes after the customer cancels is refunded.jsonl"}
```

The same holds at a limit: inventory's `Held` trace holds an order with no lines, so an implementation that refuses to hold the last units on the shelf passes every replayed trace, and fails the trace of `a paid order for the last units is confirmed`.
So write end-to-end tests for the runs your users depend on, and verify their traces too.

## Read a line you do not know

```sh
gleam run -m tazuna -- explain Prove.unproved
```

`explain` prints what a kind of line means, its exit code, its fields, and the theorems behind it.
