//// Payments: charges customers at the payment gateway, and refunds them.
////
//// When orders publishes `PaymentDue`, payments charges the amount. If the
//// order is cancelled, payments refunds a captured charge, including one
//// the gateway captures after the cancellation.

import gleam/option.{type Option, None, Some}
import shop_spec/shared.{type Caller, type OrderEvent, Staff}
import tazuna.{type Ctx, type Id, type QueryCtx}
import tazuna/table.{type Table}

pub type Status {
  Charging
  Captured(transaction: String)
  Declined
  Refunding(transaction: String)
  Refunded
  /// The gateway refused the refund; staff refund the customer by hand.
  RefundRefused(transaction: String)
}

/// A charge for one order: the amount in cents, where it stands, and whether
/// the order was cancelled.
pub type Payment {
  Payment(amount: Int, status: Status, cancelled: Bool)
}

pub type Records {
  Records(payments: Table(Id, Payment))
}

pub type Event {
  ChargeStarted(order: Id, amount: Int)
  ChargeCaptured(order: Id, transaction: String)
  ChargeDeclined(order: Id)
  RefundStarted(order: Id, transaction: String)
  RefundDone(order: Id)
  RefundFailed(order: Id)
  OrderNews(news: OrderEvent)
}

pub type Rejection {
  AlreadyCharged
  AmountNotPositive
  NothingToRefund
}

pub type Due {
  Due(order: Id, amount: Int)
}

/// A charge at the gateway, in cents. The order is the idempotency key.
pub type Charge {
  Charge(order: Id, amount: Int)
}

pub type Receipt {
  Receipt(transaction: String)
}

pub type Refusal {
  CardDeclined
  InsufficientFunds
}

pub type Refund {
  Refund(transaction: String, amount: Int)
}

pub type RefundRefusal {
  RefundWindowClosed
}

pub fn charge() -> tazuna.ExternalCommand(Charge, Receipt, Refusal) {
  tazuna.external_command(name: "charge")
}

pub fn refund() -> tazuna.ExternalCommand(Refund, Nil, RefundRefusal) {
  tazuna.external_command(name: "refund")
}

fn update(records: Records, id: Id, change: fn(Payment) -> Payment) -> Records {
  case table.get(records.payments, id) {
    Some(payment) ->
      Records(payments: table.insert(records.payments, id, change(payment)))
    None -> records
  }
}

fn set_status(records: Records, id: Id, status: Status) -> Records {
  update(records, id, fn(payment) { Payment(..payment, status: status) })
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    ChargeStarted(order, amount) ->
      Records(payments: table.insert(
        records.payments,
        order,
        Payment(amount: amount, status: Charging, cancelled: False),
      ))
    ChargeCaptured(order, transaction) ->
      set_status(records, order, Captured(transaction))
    ChargeDeclined(order) -> set_status(records, order, Declined)
    RefundStarted(order, transaction) ->
      set_status(records, order, Refunding(transaction))
    RefundDone(order) -> set_status(records, order, Refunded)
    RefundFailed(order) ->
      update(records, order, fn(payment) {
        case payment.status {
          Refunding(transaction) ->
            Payment(..payment, status: RefundRefused(transaction))
          _ -> payment
        }
      })
    OrderNews(shared.OrderCancelled(order)) ->
      update(records, order, fn(payment) { Payment(..payment, cancelled: True) })
    OrderNews(_) -> records
  }
}

/// Starts the charge for an order, once. Orders never asks for an amount that
/// is not positive; if it did, no outcome is published and the order's payment
/// deadline cancels it.
fn take() -> tazuna.Command(Records, Event, Caller, Due, Rejection) {
  tazuna.command(
    name: "take",
    callers: [tazuna.Own],
    accepts: fn(_input) { [] },
    decide: fn(ctx: Ctx(Records, Due, Caller)) {
      let Due(order, amount) = ctx.input
      use <- tazuna.require(
        table.get(ctx.records.payments, order) == None,
        or: AlreadyCharged,
      )
      use <- tazuna.require(amount > 0, or: AmountNotPositive)
      Ok([ChargeStarted(order, amount)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

/// Starts the refund of a captured charge.
fn give_back() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "give back",
    callers: [tazuna.Own],
    accepts: fn(_id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use payment <- table.lookup(
        ctx.records.payments,
        ctx.input,
        or: NothingToRefund,
      )
      case payment.status {
        Captured(transaction) -> Ok([RefundStarted(ctx.input, transaction)])
        _ -> Error(NothingToRefund)
      }
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

fn payment_status() -> tazuna.Query(Records, Caller, Id, Option(Status)) {
  tazuna.query(
    name: "payment status",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(_id) { [] },
    resolve: fn(ctx: QueryCtx(Records, Id, Caller)) {
      case table.get(ctx.records.payments, ctx.input) {
        Some(payment) -> Some(payment.status)
        None -> None
      }
    },
  )
}

fn refund_if_cancelled(
  records: Records,
  order: Id,
) -> List(tazuna.Effect(Event)) {
  case table.get(records.payments, order) {
    Some(Payment(status: Captured(_), cancelled: True, ..)) -> [
      tazuna.send_command(
        command: give_back(),
        input: order,
        on_answer: fn(_answer) { [] },
      ),
    ]
    _ -> []
  }
}

/// Talks to the gateway: charges what orders asks for, and refunds the
/// charge of a cancelled order, whether the cancellation comes before or
/// after the capture.
fn gateway() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "gateway",
    react: fn(ctx: tazuna.ReactionCtx(Records), event: Event) {
      case event {
        OrderNews(shared.PaymentDue(order, amount)) -> [
          tazuna.send_command(
            command: take(),
            input: Due(order, amount),
            on_answer: fn(_answer) { [] },
          ),
        ]
        ChargeStarted(order, amount) -> [
          tazuna.request_command(
            command: charge(),
            input: Charge(order, amount),
            on_answer: fn(answer) {
              case answer {
                Ok(receipt) -> [ChargeCaptured(order, receipt.transaction)]
                Error(_) -> [ChargeDeclined(order)]
              }
            },
          ),
        ]
        RefundStarted(order, transaction) ->
          case table.get(ctx.records.payments, order) {
            Some(payment) -> [
              tazuna.request_command(
                command: refund(),
                input: Refund(transaction, payment.amount),
                on_answer: fn(answer) {
                  case answer {
                    Ok(Nil) -> [RefundDone(order)]
                    Error(_) -> [RefundFailed(order)]
                  }
                },
              ),
            ]
            None -> []
          }
        ChargeCaptured(order, _) -> refund_if_cancelled(ctx.records, order)
        OrderNews(shared.OrderCancelled(order)) ->
          refund_if_cancelled(ctx.records, order)
        _ -> []
      }
    },
  )
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "payments",
    init: Records(payments: table.new()),
    apply: apply,
    subscribes: [tazuna.subscribe(to: shared.order_events(), wrap: OrderNews)],
    declares: [
      tazuna.declare_command(take()),
      tazuna.declare_command(give_back()),
      tazuna.declare_query(payment_status()),
      tazuna.declare_source(shared.payment_events()),
    ],
    machines: [],
    reactions: [gateway()],
    invariants: fn(records: Records) {
      [
        #(
          "every amount is positive",
          table.all(records.payments, satisfying: fn(_id, payment: Payment) {
            payment.amount > 0
          }),
        ),
        #(
          "no cancelled order keeps its money",
          table.all(records.payments, satisfying: fn(_id, payment: Payment) {
            case payment {
              Payment(status: Captured(_), cancelled: True, ..) -> False
              _ -> True
            }
          }),
        ),
      ]
    },
    responses: [],
    cascade: 1,
    scenarios: [],
  )
}

/// How far prove, explore and search look in payments.
pub fn scope() -> tazuna.Scope {
  tazuna.scope(
    service: service(),
    creates: [
      tazuna.create(
        table: fn(records: Records) { records.payments },
        at_most: 2,
      ),
    ],
    others_at_most: 2,
    steps: 3,
    explore_depth: 6,
    explore_states: 10_000,
    waits: [],
    values: [
      tazuna.values(
        of: tazuna.declare_source(shared.order_events()),
        ints: [0, 1],
        strings: [],
      ),
      tazuna.values(
        of: tazuna.declare_command(take()),
        ints: [0, 1],
        strings: [],
      ),
      tazuna.values(
        of: tazuna.declare_external_command(charge()),
        ints: [],
        strings: ["", "T-1"],
      ),
    ],
  )
}
