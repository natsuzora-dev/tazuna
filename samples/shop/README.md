# The shop sample

This sample is a small online shop, sized like a system a team would really specify: three services that talk through events, two outside systems, a deadline, and money.
It takes the spec through every tazuna command and shows what each stage found while the spec was written.
`spec/` holds the spec, a Gleam project.
An implementation of the shop, which `verify` will compare with the spec, comes in a later change.

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

You need Gleam and Erlang/OTP.
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
It asks 312 questions and takes about 14 seconds.

The six invariants hold in the initial state:

```json
{"assumes":[],"kind":"Prove.proved","service":"payments","step":"init","target":"invariant no cancelled order keeps its money"}
```

162 lines read `Prove.withinBounds`: no input breaks the target in any state that fits the model, such as three orders and two prices in orders.
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

### The lines prove leaves open

Nine lines read `Prove.unproved`, so the command exits 2.
Each is a pair of own commands, such as two `take` commands for the same order with different amounts.
If one step queued both, the result would depend on which runs first.

No step of this spec queues such a pair.
Each event starts at most one own command for an order, and each `cancel for` that the reaction or the deadline sends has a fixed reason.
`prove` does not yet see either fact, so it asks about every pair the code could send.

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

The implementation of the shop comes in a later change.
`verify` will compare its logs with the spec, as the todo sample shows.

## Read a line you do not know

```sh
gleam run -m tazuna -- explain Prove.unproved
```

`explain` prints what a kind of line means, its exit code, its fields, and the theorems behind it.
