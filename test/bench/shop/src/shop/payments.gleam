//// Payments: once inventory reserves an order, payments asks the gateway
//// for the customer's fraud score, then charges the order's total. A
//// cancelled order is voided before the charge or refunded after it. Each
//// gateway call gives up after two minutes.

import gleam/option.{type Option, None, Some}
import shop/shared.{
  type Caller, type OrderCancelled, type OrderPlaced, type Reservation, Staff,
}
import tazuna.{type Ctx, type Id, type MachineCtx, type QueryCtx}
import tazuna/bag
import tazuna/table.{type Table}

pub type PayState {
  Awaiting
  Screening
  Charging
  Captured
  Failed
  Voided
  Refunding
  Refunded
}

pub type Payment {
  Payment(
    customer: String,
    amount: Int,
    state: PayState,
    transaction: Option(String),
  )
}

pub type Records {
  Records(payments: Table(Id, Payment))
}

pub type Event {
  Ordered(placed: OrderPlaced)
  StockHeld(reservation: Reservation)
  Withdrawn(cancelled: OrderCancelled)
  ScreeningStarted(order: Id)
  RiskScored(order: Id, score: Int)
  ChargeSucceeded(order: Id, transaction: String)
  ChargeFailed(order: Id, reason: String)
  PaymentVoided(order: Id)
  RefundStarted(order: Id)
  RefundSucceeded(order: Id)
  RefundFailed(order: Id)
}

pub type Rejection {
  UnknownPayment
  NotAwaiting
  NotCaptured
  NotFailed
  Settled
  NotCalling
}

pub type Call {
  Calling
  TimedOut
}

const riskiest: Int = 80

fn state_of(records: Records, order: Id) -> Option(PayState) {
  case table.get(records.payments, order) {
    Some(payment) -> Some(payment.state)
    None -> None
  }
}

fn update(
  records: Records,
  order: Id,
  from: List(PayState),
  change: fn(Payment) -> Payment,
) -> Records {
  case table.get(records.payments, order) {
    Some(payment) ->
      case bag.contains(bag.from_list(from), payment.state) {
        True ->
          Records(payments: table.insert(
            records.payments,
            order,
            change(payment),
          ))
        False -> records
      }
    None -> records
  }
}

fn moved(to: PayState) -> fn(Payment) -> Payment {
  fn(payment: Payment) { Payment(..payment, state: to) }
}

fn apply(records: Records, event: Event) -> Records {
  case event {
    Ordered(placed) ->
      case table.get(records.payments, placed.order) {
        Some(_) -> records
        None ->
          Records(payments: table.insert(
            records.payments,
            placed.order,
            Payment(
              customer: placed.customer,
              amount: placed.total,
              state: Awaiting,
              transaction: None,
            ),
          ))
      }
    StockHeld(_) | Withdrawn(_) -> records
    ScreeningStarted(order) ->
      update(records, order, [Awaiting, Failed], moved(Screening))
    RiskScored(order, score) ->
      case score <= riskiest {
        True -> update(records, order, [Screening], moved(Charging))
        False -> update(records, order, [Screening], moved(Failed))
      }
    ChargeSucceeded(order, transaction) ->
      update(records, order, [Charging], fn(payment: Payment) {
        Payment(..payment, state: Captured, transaction: Some(transaction))
      })
    ChargeFailed(order, _reason) ->
      update(records, order, [Screening, Charging], moved(Failed))
    PaymentVoided(order) ->
      update(
        records,
        order,
        [Awaiting, Screening, Charging, Failed],
        moved(Voided),
      )
    RefundStarted(order) -> update(records, order, [Captured], moved(Refunding))
    RefundSucceeded(order) ->
      update(records, order, [Refunding], moved(Refunded))
    RefundFailed(order) -> update(records, order, [Refunding], moved(Captured))
  }
}

fn calling(state: PayState) -> Bool {
  state == Screening || state == Charging || state == Refunding
}

pub fn start_screening() -> tazuna.Command(
  Records,
  Event,
  Caller,
  Id,
  Rejection,
) {
  tazuna.command(
    name: "start screening",
    callers: [tazuna.Own],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use payment <- table.lookup(
        ctx.records.payments,
        ctx.input,
        or: UnknownPayment,
      )
      use <- tazuna.require(payment.state == Awaiting, or: NotAwaiting)
      Ok([ScreeningStarted(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #(
          "the payment is screened",
          state_of(after, ctx.input) == Some(Screening),
        ),
      ]
    },
  )
}

/// Staff try a failed payment again from the fraud check.
pub fn retry_payment() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "retry payment",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use payment <- table.lookup(
        ctx.records.payments,
        ctx.input,
        or: UnknownPayment,
      )
      use <- tazuna.require(payment.state == Failed, or: NotFailed)
      Ok([ScreeningStarted(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #(
          "the payment is screened",
          state_of(after, ctx.input) == Some(Screening),
        ),
      ]
    },
  )
}

pub fn refund_payment() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "refund payment",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use payment <- table.lookup(
        ctx.records.payments,
        ctx.input,
        or: UnknownPayment,
      )
      use <- tazuna.require(payment.state == Captured, or: NotCaptured)
      Ok([RefundStarted(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [#("the refund runs", state_of(after, ctx.input) == Some(Refunding))]
    },
  )
}

/// A cancelled order: refund what was taken, void what was not.
pub fn withdraw() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "withdraw",
    callers: [tazuna.Own],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use payment <- table.lookup(
        ctx.records.payments,
        ctx.input,
        or: UnknownPayment,
      )
      case payment.state {
        Captured -> Ok([RefundStarted(ctx.input)])
        Awaiting | Screening | Charging | Failed ->
          Ok([PaymentVoided(ctx.input)])
        Voided | Refunding | Refunded -> Error(Settled)
      }
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #(
          "nothing more is charged",
          state_of(after, ctx.input) == Some(Voided)
            || state_of(after, ctx.input) == Some(Refunding),
        ),
      ]
    },
  )
}

/// A gateway call that took too long fails the step it was for.
pub fn give_up() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "give up",
    callers: [tazuna.Own],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use payment <- table.lookup(
        ctx.records.payments,
        ctx.input,
        or: UnknownPayment,
      )
      case payment.state {
        Screening | Charging -> Ok([ChargeFailed(ctx.input, "gateway timeout")])
        Refunding -> Ok([RefundFailed(ctx.input)])
        _ -> Error(NotCalling)
      }
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

pub fn payment_state() -> tazuna.Query(Records, Caller, Id, Option(PayState)) {
  tazuna.query(
    name: "payment state",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    resolve: fn(ctx: QueryCtx(Records, Id, Caller)) {
      state_of(ctx.records, ctx.input)
    },
  )
}

fn charge_flow() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "charge flow",
    react: fn(ctx: tazuna.ReactionCtx(Records), event: Event) {
      case event {
        StockHeld(shared.Reserved(order)) -> [
          tazuna.send_command(
            command: start_screening(),
            input: order,
            on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
          ),
        ]
        Withdrawn(cancelled) ->
          case state_of(ctx.records, cancelled.order) {
            Some(_) -> [
              tazuna.send_command(
                command: withdraw(),
                input: cancelled.order,
                on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
              ),
            ]
            None -> []
          }
        _ -> []
      }
    },
  )
}

/// One instance per payment waiting on the gateway. Entering `Calling` makes
/// the call the payment's state needs; a fraud score that lets the charge go
/// ahead enters `Calling` again for the charge.
fn gateway_call() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "gateway call",
    instances: fn(records: Records) {
      table.keys(
        table.filter(records.payments, keeping: fn(_order, payment: Payment) {
          calling(payment.state)
        }),
      )
    },
    initial: Calling,
    on: fn(ctx: MachineCtx(Id, Call, Records), event: Event) {
      case event {
        RiskScored(order:, ..) if order == ctx.key -> tazuna.Enter(Calling)
        _ -> tazuna.Stay
      }
    },
    after: fn(ctx: MachineCtx(Id, Call, Records)) {
      case ctx.state {
        Calling -> Some(tazuna.Timer(after: 2 * shared.minute, enter: TimedOut))
        TimedOut -> None
      }
    },
    effect: fn(ctx: MachineCtx(Id, Call, Records)) {
      let order = ctx.key
      case ctx.state, table.get(ctx.records.payments, order) {
        Calling, Some(payment) ->
          case payment.state {
            Screening ->
              Some(
                tazuna.request_query(
                  query: shared.risk_score(),
                  input: shared.RiskQuestion(
                    customer: payment.customer,
                    amount: payment.amount,
                  ),
                  on_answer: fn(score: Int) { [RiskScored(order, score)] },
                ),
              )
            Charging ->
              Some(
                tazuna.request_command(
                  command: shared.charge(),
                  input: shared.Charge(
                    order: order,
                    amount: payment.amount,
                    currency: "JPY",
                  ),
                  on_answer: fn(
                    answer: Result(shared.Receipt, shared.ChargeRefused),
                  ) {
                    case answer {
                      Ok(receipt) -> [
                        ChargeSucceeded(order, receipt.transaction),
                      ]
                      Error(shared.CardDeclined(code)) -> [
                        ChargeFailed(order, "card declined: " <> code),
                      ]
                      Error(shared.GatewayDown) -> [
                        ChargeFailed(order, "gateway down"),
                      ]
                    }
                  },
                ),
              )
            Refunding ->
              case payment.transaction {
                Some(transaction) ->
                  Some(
                    tazuna.request_command(
                      command: shared.refund(),
                      input: shared.Refund(
                        transaction: transaction,
                        amount: payment.amount,
                      ),
                      on_answer: fn(answer: Result(Nil, shared.ChargeRefused)) {
                        case answer {
                          Ok(Nil) -> [RefundSucceeded(order)]
                          Error(_) -> [RefundFailed(order)]
                        }
                      },
                    ),
                  )
                None -> None
              }
            _ -> None
          }
        TimedOut, _ ->
          Some(
            tazuna.send_command(
              command: give_up(),
              input: order,
              on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
            ),
          )
        _, _ -> None
      }
    },
    invariants: fn(_ctx: MachineCtx(Id, Call, Records)) { [] },
  )
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "payments",
    init: Records(payments: table.new()),
    apply: apply,
    subscribes: [
      tazuna.subscribe(to: shared.order_placed(), wrap: fn(placed: OrderPlaced) {
        Ordered(placed)
      }),
      tazuna.subscribe(to: shared.reservations(), wrap: fn(news: Reservation) {
        StockHeld(news)
      }),
      tazuna.subscribe(
        to: shared.order_cancelled(),
        wrap: fn(cancelled: OrderCancelled) { Withdrawn(cancelled) },
      ),
    ],
    declares: [
      tazuna.declare_command(start_screening()),
      tazuna.declare_command(retry_payment()),
      tazuna.declare_command(refund_payment()),
      tazuna.declare_command(withdraw()),
      tazuna.declare_command(give_up()),
      tazuna.declare_query(payment_state()),
      tazuna.declare_source(shared.payment_outcomes()),
    ],
    machines: [gateway_call()],
    reactions: [charge_flow()],
    invariants: fn(records: Records) {
      [
        #(
          "every amount is positive",
          table.all(records.payments, satisfying: fn(_order, payment: Payment) {
            payment.amount > 0
          }),
        ),
        #(
          "money taken has a transaction",
          table.all(records.payments, satisfying: fn(_order, payment: Payment) {
            case payment.state {
              Captured | Refunding | Refunded -> payment.transaction != None
              _ -> True
            }
          }),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "screening ends within 5 minutes",
        after: fn(event: Event) {
          case event {
            ScreeningStarted(..) -> True
            _ -> False
          }
        },
        then: fn(trigger: Event, event: Event) {
          case trigger, event {
            ScreeningStarted(order:), ChargeSucceeded(order: done, ..) ->
              done == order
            ScreeningStarted(order:), ChargeFailed(order: done, ..) ->
              done == order
            ScreeningStarted(order:), PaymentVoided(order: done) ->
              done == order
            _, _ -> False
          }
        },
        within: 5 * shared.minute,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [
        tazuna.create(
          table: fn(records: Records) { records.payments },
          at_most: 3,
        ),
      ],
      items: 2,
      cascade: 2,
      steps: 4,
    ),
    scenarios: [],
  )
}
