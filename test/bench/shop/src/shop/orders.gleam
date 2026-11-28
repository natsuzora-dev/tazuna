//// Orders: customers place and cancel orders. An order waits for stock, then
//// for payment, then for delivery; an order not paid within 30 minutes is
//// cancelled. Orders learns prices from the catalog and outcomes from
//// inventory, payments and shipping through their events.

import gleam/option.{type Option, None, Some}
import shop/shared.{
  type Caller, type Delivery, type Line, type PaymentOutcome, type PriceChanged,
  type Reservation, Customer, Staff,
}
import tazuna.{type Ctx, type Id, type MachineCtx, type QueryCtx, type TimerCtx}
import tazuna/bag.{type Bag}
import tazuna/duration
import tazuna/instant.{type Instant}
import tazuna/table.{type Table}

pub type Status {
  AwaitingStock
  AwaitingPayment
  Paid
  Delivered
  Returned
  Cancelled
}

pub type Order {
  Order(
    customer: String,
    email: String,
    address: String,
    lines: Bag(Line),
    total: Int,
    status: Status,
    pay_by: Instant,
  )
}

/// Orders by id, and the catalog's current price per SKU in cents.
pub type Records {
  Records(orders: Table(Id, Order), prices: Table(String, Int))
}

pub type Event {
  Placed(
    order: Id,
    customer: String,
    email: String,
    address: String,
    lines: Bag(Line),
    total: Int,
  )
  OrderCancelled(order: Id, reason: String)
  StockNews(reservation: Reservation)
  PaymentNews(outcome: PaymentOutcome)
  DeliveryNews(delivery: Delivery)
  PriceNews(change: PriceChanged)
}

pub type Rejection {
  StalePrice
  UnknownOrder
  TooLate
}

pub type NewOrder {
  NewOrder(customer: String, email: String, address: String, lines: Bag(Line))
}

pub type Cancellation {
  Cancellation(order: Id, reason: String)
}

pub type Deadline {
  Open
  Expired
}

fn line_total(line: Line) -> Int {
  line.quantity * line.unit_price
}

fn set_status(records: Records, order: Id, status: Status) -> Records {
  case table.get(records.orders, order) {
    Some(found) ->
      Records(
        ..records,
        orders: table.insert(
          records.orders,
          order,
          Order(..found, status: status),
        ),
      )
    None -> records
  }
}

/// Moves the order on only from the status the news is about, so late or
/// repeated news leaves it alone.
fn advance(records: Records, order: Id, from: Status, to: Status) -> Records {
  case table.get(records.orders, order) {
    Some(found) if found.status == from -> set_status(records, order, to)
    _ -> records
  }
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    Placed(order, customer, email, address, lines, total) ->
      Records(
        ..records,
        orders: table.insert(
          records.orders,
          order,
          Order(
            customer: customer,
            email: email,
            address: address,
            lines: lines,
            total: total,
            status: AwaitingStock,
            pay_by: instant.add(ctx.now, duration.minutes(30)),
          ),
        ),
      )
    OrderCancelled(order, _reason) -> set_status(records, order, Cancelled)
    StockNews(shared.Reserved(order)) ->
      advance(records, order, AwaitingStock, AwaitingPayment)
    StockNews(shared.Unavailable(..)) -> records
    PaymentNews(shared.Captured(order, _amount)) ->
      advance(records, order, AwaitingPayment, Paid)
    PaymentNews(shared.Declined(..)) -> records
    PaymentNews(shared.Refunded(..)) -> records
    DeliveryNews(shared.Delivered(order)) ->
      advance(records, order, Paid, Delivered)
    DeliveryNews(shared.Returned(order)) ->
      advance(records, order, Paid, Returned)
    PriceNews(shared.PriceChanged(sku, price)) ->
      Records(..records, prices: table.insert(records.prices, sku, price))
  }
}

fn open(status: Status) -> Bool {
  status == AwaitingStock || status == AwaitingPayment
}

fn cancellable(status: Status) -> Bool {
  open(status) || status == Paid
}

pub fn place_order() -> tazuna.Command(
  Records,
  Event,
  Caller,
  NewOrder,
  Rejection,
) {
  tazuna.command(
    name: "place order",
    callers: [tazuna.Outside(Customer)],
    accepts: fn(input: NewOrder) {
      [
        #("customer is named", input.customer != ""),
        #("email is given", tazuna.length(input.email) >= 3),
        #("address is given", input.address != ""),
        #("at least one line", bag.size(input.lines) >= 1),
        #(
          "1 to 10 of each product",
          bag.all(input.lines, satisfying: fn(line: Line) {
            line.quantity >= 1 && line.quantity <= 10
          }),
        ),
        #(
          "prices are positive",
          bag.all(input.lines, satisfying: fn(line: Line) {
            line.unit_price > 0
          }),
        ),
      ]
    },
    decide: fn(ctx: Ctx(Records, NewOrder, Caller)) {
      use <- tazuna.require(
        bag.all(ctx.input.lines, satisfying: fn(line: Line) {
          table.get(ctx.records.prices, line.sku) == Some(line.unit_price)
        }),
        or: StalePrice,
      )
      Ok([
        Placed(
          order: tazuna.fresh(ctx.fresh, 0),
          customer: ctx.input.customer,
          email: ctx.input.email,
          address: ctx.input.address,
          lines: ctx.input.lines,
          total: bag.sum(ctx.input.lines, of: line_total),
        ),
      ])
    },
    ensures: fn(ctx: Ctx(Records, NewOrder, Caller), after: Records) {
      [
        #(
          "the order waits for stock",
          case table.get(after.orders, tazuna.fresh(ctx.fresh, 0)) {
            Some(order) -> order.status == AwaitingStock
            None -> False
          },
        ),
      ]
    },
  )
}

pub fn cancel_order() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "cancel order",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use order <- table.lookup(ctx.records.orders, ctx.input, or: UnknownOrder)
      use <- tazuna.require(cancellable(order.status), or: TooLate)
      let reason = case ctx.caller {
        tazuna.Outside(Staff) -> "cancelled by staff"
        _ -> "cancelled by customer"
      }
      Ok([OrderCancelled(ctx.input, reason)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #("the order is cancelled", case table.get(after.orders, ctx.input) {
          Some(order) -> order.status == Cancelled
          None -> False
        }),
      ]
    },
  )
}

/// The service cancels an order itself when stock or payment fails or the
/// payment deadline passes.
pub fn cancel_for() -> tazuna.Command(
  Records,
  Event,
  Caller,
  Cancellation,
  Rejection,
) {
  tazuna.command(
    name: "cancel for",
    callers: [tazuna.Own],
    accepts: fn(input: Cancellation) {
      [#("a reason is given", input.reason != "")]
    },
    decide: fn(ctx: Ctx(Records, Cancellation, Caller)) {
      use order <- table.lookup(
        ctx.records.orders,
        ctx.input.order,
        or: UnknownOrder,
      )
      use <- tazuna.require(open(order.status), or: TooLate)
      Ok([OrderCancelled(ctx.input.order, ctx.input.reason)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

pub fn order_status() -> tazuna.Query(Records, Caller, Id, Option(Status)) {
  tazuna.query(
    name: "order status",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    resolve: fn(ctx: QueryCtx(Records, Id, Caller)) {
      case table.get(ctx.records.orders, ctx.input) {
        Some(order) -> Some(order.status)
        None -> None
      }
    },
  )
}

/// How many of a customer's orders are still waiting for stock or payment.
pub fn open_orders() -> tazuna.Query(Records, Caller, String, Int) {
  tazuna.query(
    name: "open orders",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(customer: String) { [#("customer is named", customer != "")] },
    resolve: fn(ctx: QueryCtx(Records, String, Caller)) {
      table.count(ctx.records.orders, where: fn(_id, order: Order) {
        order.customer == ctx.input && open(order.status)
      })
    },
  )
}

/// One instance per order waiting for stock or payment: at its pay-by time,
/// the order is cancelled.
fn payment_deadline() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "payment deadline",
    instances: fn(records: Records) {
      table.keys(
        table.filter(records.orders, keeping: fn(_id, order: Order) {
          open(order.status)
        }),
      )
    },
    initial: Open,
    on: fn(_ctx: MachineCtx(Id, Deadline, Records), _event: Event) {
      tazuna.Stay
    },
    timer: fn(ctx: TimerCtx(Id, Deadline, Records)) {
      case ctx.state, table.get(ctx.records.orders, ctx.key) {
        Open, Some(order) ->
          Some(tazuna.Timer(at: order.pay_by, enter: Expired))
        _, _ -> None
      }
    },
    effect: fn(ctx: MachineCtx(Id, Deadline, Records)) {
      case ctx.state {
        Open -> None
        Expired ->
          Some(
            tazuna.send_command(
              command: cancel_for(),
              input: Cancellation(order: ctx.key, reason: "not paid in time"),
              on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
            ),
          )
      }
    },
    invariants: fn(ctx: MachineCtx(Id, Deadline, Records)) {
      [#("an expired order is already cancelled", ctx.state == Open)]
    },
  )
}

fn mail_for(
  records: Records,
  order: Id,
  subject: String,
) -> List(tazuna.Effect(Event)) {
  case table.get(records.orders, order) {
    Some(found) -> [
      tazuna.request_command(
        command: shared.send_mail(),
        input: shared.Mail(
          to: found.email,
          subject: subject,
          body: "Hello " <> found.customer <> ", your order: " <> subject,
        ),
        on_answer: fn(_answer: Result(Nil, shared.MailRefused)) { [] },
      ),
    ]
    None -> []
  }
}

/// Mails the customer about their order, and cancels an order whose stock or
/// payment failed.
fn follow_up() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "follow up",
    react: fn(ctx: tazuna.ReactionCtx(Records), event: Event) {
      case event {
        Placed(order:, ..) -> mail_for(ctx.records, order, "received")
        OrderCancelled(order:, ..) -> mail_for(ctx.records, order, "cancelled")
        StockNews(shared.Unavailable(order, _missing)) -> [
          tazuna.send_command(
            command: cancel_for(),
            input: Cancellation(order: order, reason: "out of stock"),
            on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
          ),
        ]
        PaymentNews(shared.Declined(order, reason)) -> [
          tazuna.send_command(
            command: cancel_for(),
            input: Cancellation(
              order: order,
              reason: "payment declined: " <> reason,
            ),
            on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
          ),
        ]
        DeliveryNews(shared.Delivered(order)) ->
          mail_for(ctx.records, order, "delivered")
        _ -> []
      }
    },
  )
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "orders",
    init: Records(orders: table.new(), prices: table.new()),
    apply: apply,
    subscribes: [
      tazuna.subscribe(to: shared.reservations(), wrap: fn(news: Reservation) {
        StockNews(news)
      }),
      tazuna.subscribe(
        to: shared.payment_outcomes(),
        wrap: fn(news: PaymentOutcome) { PaymentNews(news) },
      ),
      tazuna.subscribe(to: shared.deliveries(), wrap: fn(news: Delivery) {
        DeliveryNews(news)
      }),
      tazuna.subscribe(to: shared.price_changes(), wrap: fn(news: PriceChanged) {
        PriceNews(news)
      }),
    ],
    declares: [
      tazuna.declare_command(place_order()),
      tazuna.declare_command(cancel_order()),
      tazuna.declare_command(cancel_for()),
      tazuna.declare_query(order_status()),
      tazuna.declare_query(open_orders()),
      tazuna.declare_source(shared.order_placed()),
      tazuna.declare_source(shared.order_cancelled()),
    ],
    machines: [payment_deadline()],
    reactions: [follow_up()],
    invariants: fn(records: Records) {
      [
        #(
          "every order has a line",
          table.all(records.orders, satisfying: fn(_id, order: Order) {
            bag.size(order.lines) >= 1
          }),
        ),
        #(
          "every total is the sum of its lines",
          table.all(records.orders, satisfying: fn(_id, order: Order) {
            order.total == bag.sum(order.lines, of: line_total)
          }),
        ),
        #(
          "every total is positive",
          table.all(records.orders, satisfying: fn(_id, order: Order) {
            order.total > 0
          }),
        ),
        #(
          "every known price is positive",
          table.all(records.prices, satisfying: fn(_sku, price: Int) {
            price > 0
          }),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "a placed order is paid or cancelled within 30 minutes",
        after: fn(event: Event) {
          case event {
            Placed(..) -> True
            _ -> False
          }
        },
        then: fn(trigger: Event, event: Event) {
          case trigger, event {
            Placed(order:, ..), PaymentNews(shared.Captured(paid, _)) ->
              paid == order
            Placed(order:, ..), OrderCancelled(order: cancelled, ..) ->
              cancelled == order
            _, _ -> False
          }
        },
        within: duration.minutes(30),
        deadline: fn(records: Records, trigger: Event) {
          case trigger {
            Placed(order:, ..) ->
              case table.get(records.orders, order) {
                Some(found) if found.status == AwaitingStock ->
                  Some(found.pay_by)
                Some(found) if found.status == AwaitingPayment ->
                  Some(found.pay_by)
                _ -> None
              }
            _ -> None
          }
        },
      ),
    ],
    cascade: 2,
    scenarios: [an_order_is_paid(), an_unpaid_order_expires()],
  )
}

fn mug() -> Line {
  shared.Line(sku: "MUG-01", quantity: 2, unit_price: 1800)
}

fn an_order() -> NewOrder {
  NewOrder(
    customer: "Aiko",
    email: "aiko@example.com",
    address: "1-2-3 Shibuya, Tokyo",
    lines: bag.from_list([mug()]),
  )
}

fn an_order_is_paid() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "an order is paid", steps: [
    tazuna.step_command(
      command: place_order(),
      caller: Customer,
      input: an_order(),
    ),
    tazuna.step_event(
      source: shared.price_changes(),
      value: shared.PriceChanged(sku: "MUG-01", price: 1800),
    ),
    {
      use placed <- tazuna.step_command_then(
        command: place_order(),
        caller: Customer,
        input: an_order(),
      )
      let order = tazuna.fresh(placed, 0)
      [
        tazuna.step_answer_command(
          command: shared.send_mail(),
          sender: tazuna.from_reaction(reaction: follow_up()),
          with: Ok(Nil),
        ),
        tazuna.step_event(
          source: shared.reservations(),
          value: shared.Reserved(order),
        ),
        tazuna.step_event(
          source: shared.payment_outcomes(),
          value: shared.Captured(order, 3600),
        ),
        tazuna.step_query(query: order_status(), caller: Customer, input: order),
        tazuna.step_wait(for: duration.minutes(30)),
        tazuna.step_command(
          command: cancel_order(),
          caller: Staff,
          input: order,
        ),
      ]
    },
  ])
}

fn an_unpaid_order_expires() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "an unpaid order expires", steps: [
    tazuna.step_event(
      source: shared.price_changes(),
      value: shared.PriceChanged(sku: "MUG-01", price: 1800),
    ),
    tazuna.step_command(
      command: place_order(),
      caller: Customer,
      input: an_order(),
    ),
    tazuna.step_wait(for: duration.minutes(30)),
    tazuna.step_query(query: open_orders(), caller: Customer, input: "Aiko"),
  ])
}

/// How far prove and generate look in this service.
pub fn scope() -> tazuna.Scope {
  tazuna.scope(
    service: service(),
    creates: [
      tazuna.create(table: fn(records: Records) { records.orders }, at_most: 3),
      tazuna.create(table: fn(records: Records) { records.prices }, at_most: 3),
    ],
    others_at_most: 2,
    steps: 4,
    explore_depth: 0,
    explore_states: 1,
    waits: [],
    values: [],
  )
}
