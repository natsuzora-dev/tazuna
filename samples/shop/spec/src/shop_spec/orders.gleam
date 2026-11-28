//// Orders: staff set prices, and customers place and cancel orders.
////
//// An order waits for inventory to hold its stock, then for payments to
//// capture its total. Fifteen minutes after it is placed, an order that is
//// still waiting is cancelled. The customer gets a mail when the order is
//// confirmed or cancelled.

import gleam/option.{type Option, None, Some}
import shop_spec/shared.{
  type Caller, type Line, type PaymentEvent, type StockEvent, Customer, Staff,
}
import tazuna.{type Ctx, type Id, type MachineCtx, type QueryCtx, type TimerCtx}
import tazuna/bag.{type Bag}
import tazuna/duration
import tazuna/instant.{type Instant}
import tazuna/table.{type Table}

pub type Status {
  AwaitingStock
  AwaitingPayment
  Confirmed
  Cancelled(reason: Reason)
}

pub type Reason {
  ByCustomer
  OutOfStock
  PaymentFailed
  NotPaidInTime
}

/// An order: where to mail the customer, what they bought, the total in
/// cents at the prices when they ordered, and when it must be paid by.
pub type Order {
  Order(
    email: String,
    lines: Bag(Line),
    total: Int,
    status: Status,
    pay_by: Instant,
  )
}

/// Orders by id, and the price of each product in cents by SKU.
pub type Records {
  Records(orders: Table(Id, Order), prices: Table(String, Int))
}

pub type Event {
  PriceSet(sku: String, price: Int)
  Placed(order: Id, email: String, lines: Bag(Line), total: Int)
  PaymentDue(order: Id, amount: Int)
  OrderConfirmed(order: Id)
  OrderCancelled(order: Id, reason: Reason)
  StockNews(news: StockEvent)
  PaymentNews(news: PaymentEvent)
}

pub type Rejection {
  UnknownProduct
  TooManyCheckouts
  NoSuchOrder
  NotOpen
  NotAwaitingStock
  NotAwaitingPayment
}

pub type NewPrice {
  NewPrice(sku: String, price: Int)
}

pub type NewOrder {
  NewOrder(email: String, lines: Bag(Line))
}

pub type Cancellation {
  Cancellation(order: Id, reason: Reason)
}

/// The phase of an open order's payment deadline.
pub type Deadline {
  Running
  Passed
}

/// How long a customer has to pay.
fn time_to_pay() -> duration.Duration {
  duration.minutes(15)
}

/// At most this many orders wait for stock or payment at a time. Orders
/// placed together pass their deadline together, and each passed deadline is
/// one internal step of the clock line that reaches it, so this limit is what
/// keeps a clock line within the service's `cascade`.
const checkout_limit = 3

fn open(status: Status) -> Bool {
  case status {
    AwaitingStock | AwaitingPayment -> True
    Confirmed | Cancelled(_) -> False
  }
}

fn price_of(prices: Table(String, Int), sku: String) -> Int {
  case table.get(prices, sku) {
    Some(price) -> price
    None -> 0
  }
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    PriceSet(sku, price) ->
      Records(..records, prices: table.insert(records.prices, sku, price))
    Placed(order, email, lines, total) ->
      Records(
        ..records,
        orders: table.insert(
          records.orders,
          order,
          Order(
            email: email,
            lines: lines,
            total: total,
            status: AwaitingStock,
            pay_by: instant.add(ctx.now, time_to_pay()),
          ),
        ),
      )
    PaymentDue(order, _amount) -> set_status(records, order, AwaitingPayment)
    OrderConfirmed(order) -> set_status(records, order, Confirmed)
    OrderCancelled(order, reason) ->
      set_status(records, order, Cancelled(reason))
    StockNews(_) | PaymentNews(_) -> records
  }
}

fn set_status(records: Records, id: Id, status: Status) -> Records {
  case table.get(records.orders, id) {
    Some(order) ->
      Records(
        ..records,
        orders: table.insert(records.orders, id, Order(..order, status: status)),
      )
    None -> records
  }
}

fn set_price() -> tazuna.Command(Records, Event, Caller, NewPrice, Rejection) {
  tazuna.command(
    name: "set price",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(input: NewPrice) {
      [
        #("sku is given", input.sku != ""),
        #("price is positive", input.price > 0),
      ]
    },
    decide: fn(ctx: Ctx(Records, NewPrice, Caller)) {
      Ok([PriceSet(ctx.input.sku, ctx.input.price)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

fn place_order() -> tazuna.Command(Records, Event, Caller, NewOrder, Rejection) {
  tazuna.command(
    name: "place order",
    callers: [tazuna.Outside(Customer)],
    accepts: fn(input: NewOrder) {
      [
        #("email is given", input.email != ""),
        #("an order has a line", bag.size(input.lines) >= 1),
        #(
          "each quantity is 1 to 10",
          bag.all(input.lines, satisfying: fn(line: Line) {
            line.quantity >= 1 && line.quantity <= 10
          }),
        ),
      ]
    },
    decide: fn(ctx: Ctx(Records, NewOrder, Caller)) {
      let prices = ctx.records.prices
      let checkouts =
        table.count(ctx.records.orders, where: fn(_id, order: Order) {
          open(order.status)
        })
      use <- tazuna.require(checkouts < checkout_limit, or: TooManyCheckouts)
      use <- tazuna.require(
        bag.all(ctx.input.lines, satisfying: fn(line: Line) {
          table.get(prices, line.sku) != None
        }),
        or: UnknownProduct,
      )
      let total =
        bag.sum(ctx.input.lines, of: fn(line: Line) {
          line.quantity * price_of(prices, line.sku)
        })
      Ok([
        Placed(
          order: tazuna.fresh(ctx.fresh, 0),
          email: ctx.input.email,
          lines: ctx.input.lines,
          total: total,
        ),
      ])
    },
    ensures: fn(ctx: Ctx(Records, NewOrder, Caller), after: Records) {
      [
        #(
          "the new order waits for stock",
          case table.get(after.orders, tazuna.fresh(ctx.fresh, 0)) {
            Some(order) -> order.status == AwaitingStock
            None -> False
          },
        ),
      ]
    },
  )
}

fn cancel_order() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "cancel order",
    callers: [tazuna.Outside(Customer)],
    accepts: fn(_id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use order <- table.lookup(ctx.records.orders, ctx.input, or: NoSuchOrder)
      use <- tazuna.require(open(order.status), or: NotOpen)
      Ok([OrderCancelled(ctx.input, ByCustomer)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

/// Asks payments for the total, once inventory holds the stock.
fn request_payment() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "request payment",
    callers: [tazuna.Own],
    accepts: fn(_id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use order <- table.lookup(ctx.records.orders, ctx.input, or: NoSuchOrder)
      use <- tazuna.require(order.status == AwaitingStock, or: NotAwaitingStock)
      Ok([PaymentDue(ctx.input, order.total)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

fn confirm() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "confirm",
    callers: [tazuna.Own],
    accepts: fn(_id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use order <- table.lookup(ctx.records.orders, ctx.input, or: NoSuchOrder)
      use <- tazuna.require(
        order.status == AwaitingPayment,
        or: NotAwaitingPayment,
      )
      Ok([OrderConfirmed(ctx.input)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

/// Cancels an open order for a reason of the shop's: no stock, no payment, or
/// no payment in time.
fn cancel_for() -> tazuna.Command(
  Records,
  Event,
  Caller,
  Cancellation,
  Rejection,
) {
  tazuna.command(
    name: "cancel for",
    callers: [tazuna.Own],
    accepts: fn(_input) { [] },
    decide: fn(ctx: Ctx(Records, Cancellation, Caller)) {
      let id = ctx.input.order
      use order <- table.lookup(ctx.records.orders, id, or: NoSuchOrder)
      use <- tazuna.require(open(order.status), or: NotOpen)
      Ok([OrderCancelled(id, ctx.input.reason)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

fn order_status() -> tazuna.Query(Records, Caller, Id, Option(Status)) {
  tazuna.query(
    name: "order status",
    callers: [tazuna.Outside(Customer)],
    accepts: fn(_id) { [] },
    resolve: fn(ctx: QueryCtx(Records, Id, Caller)) {
      case table.get(ctx.records.orders, ctx.input) {
        Some(order) -> Some(order.status)
        None -> None
      }
    },
  )
}

/// What the mailer is asked to send.
pub type Mail {
  Mail(to: String, subject: String)
}

pub type Undeliverable {
  Undeliverable
}

pub fn send_mail() -> tazuna.ExternalCommand(Mail, Nil, Undeliverable) {
  tazuna.external_command(name: "send")
}

/// One instance per open order. When its pay-by time passes, the order is
/// cancelled.
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
    initial: Running,
    on: fn(_ctx, _event) { tazuna.Stay },
    timer: fn(ctx: TimerCtx(Id, Deadline, Records)) {
      case ctx.state, table.get(ctx.records.orders, ctx.key) {
        Running, Some(order) ->
          Some(tazuna.Timer(at: order.pay_by, enter: Passed))
        _, _ -> None
      }
    },
    effect: fn(ctx: MachineCtx(Id, Deadline, Records)) {
      case ctx.state {
        Running -> None
        Passed ->
          Some(
            tazuna.send_command(
              command: cancel_for(),
              input: Cancellation(order: ctx.key, reason: NotPaidInTime),
              on_answer: fn(_answer) { [] },
            ),
          )
      }
    },
    invariants: fn(ctx: MachineCtx(Id, Deadline, Records)) {
      [#("a passed deadline has cancelled its order", ctx.state == Running)]
    },
  )
}

fn mail_about(
  records: Records,
  order: Id,
  subject: String,
) -> List(tazuna.Effect(Event)) {
  case table.get(records.orders, order) {
    Some(found) -> [
      tazuna.request_command(
        command: send_mail(),
        input: Mail(to: found.email, subject: subject),
        on_answer: fn(_answer) { [] },
      ),
    ]
    None -> []
  }
}

/// Moves an order on when inventory or payments report, and mails the
/// customer when it is confirmed or cancelled.
fn checkout() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "checkout",
    react: fn(ctx: tazuna.ReactionCtx(Records), event: Event) {
      case event {
        StockNews(shared.StockHeld(order)) -> [
          tazuna.send_command(
            command: request_payment(),
            input: order,
            on_answer: fn(_answer) { [] },
          ),
        ]
        StockNews(shared.OutOfStock(order)) -> [
          tazuna.send_command(
            command: cancel_for(),
            input: Cancellation(order: order, reason: OutOfStock),
            on_answer: fn(_answer) { [] },
          ),
        ]
        PaymentNews(shared.PaymentCaptured(order)) -> [
          tazuna.send_command(
            command: confirm(),
            input: order,
            on_answer: fn(_answer) { [] },
          ),
        ]
        PaymentNews(shared.PaymentFailed(order)) -> [
          tazuna.send_command(
            command: cancel_for(),
            input: Cancellation(order: order, reason: PaymentFailed),
            on_answer: fn(_answer) { [] },
          ),
        ]
        OrderConfirmed(order) ->
          mail_about(ctx.records, order, "Your order is confirmed")
        OrderCancelled(order, _reason) ->
          mail_about(ctx.records, order, "Your order is cancelled")
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
      tazuna.subscribe(to: shared.stock_events(), wrap: StockNews),
      tazuna.subscribe(to: shared.payment_events(), wrap: PaymentNews),
    ],
    declares: [
      tazuna.declare_command(set_price()),
      tazuna.declare_command(place_order()),
      tazuna.declare_command(cancel_order()),
      tazuna.declare_command(request_payment()),
      tazuna.declare_command(confirm()),
      tazuna.declare_command(cancel_for()),
      tazuna.declare_query(order_status()),
      tazuna.declare_source(shared.order_events()),
    ],
    machines: [payment_deadline()],
    reactions: [checkout()],
    invariants: fn(records: Records) {
      [
        #(
          "every price is positive",
          table.all(records.prices, satisfying: fn(_sku, price) { price > 0 }),
        ),
        #(
          "every total is positive",
          table.all(records.orders, satisfying: fn(_id, order: Order) {
            order.total > 0
          }),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "a placed order is confirmed or cancelled within 15 minutes",
        after: fn(event) {
          case event {
            Placed(..) -> True
            _ -> False
          }
        },
        then: fn(trigger, event) {
          case trigger, event {
            Placed(order:, ..), OrderConfirmed(order: done) -> done == order
            Placed(order:, ..), OrderCancelled(order: done, ..) -> done == order
            _, _ -> False
          }
        },
        within: time_to_pay(),
        deadline: fn(records: Records, trigger: Event) {
          case trigger {
            Placed(order:, ..) ->
              case table.get(records.orders, order) {
                Some(found) ->
                  case open(found.status) {
                    True -> Some(found.pay_by)
                    False -> None
                  }
                None -> None
              }
            _ -> None
          }
        },
      ),
    ],
    cascade: checkout_limit,
    scenarios: [a_paid_order_is_confirmed(), an_unpaid_order_is_cancelled()],
  )
}

/// The customer orders two mugs; inventory holds them, payments captures the
/// total, and the customer gets a mail that the order is confirmed.
fn a_paid_order_is_confirmed() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "a paid order is confirmed", steps: [
    tazuna.step_command(
      command: set_price(),
      caller: Staff,
      input: NewPrice(sku: "MUG", price: 1200),
    ),
    {
      use placed <- tazuna.step_command_then(
        command: place_order(),
        caller: Customer,
        input: NewOrder(
          email: "ann@example.com",
          lines: bag.from_list([shared.Line(sku: "MUG", quantity: 2)]),
        ),
      )
      let order = tazuna.fresh(placed, 0)
      [
        tazuna.step_event(
          source: shared.stock_events(),
          value: shared.StockHeld(order),
        ),
        tazuna.step_event(
          source: shared.payment_events(),
          value: shared.PaymentCaptured(order),
        ),
        tazuna.step_query(query: order_status(), caller: Customer, input: order),
        tazuna.step_answer_command(
          command: send_mail(),
          sender: tazuna.from_reaction(reaction: checkout()),
          with: Ok(Nil),
        ),
      ]
    },
  ])
}

/// The stock is held but the payment never arrives: fifteen minutes after the
/// order, the payment deadline cancels it.
fn an_unpaid_order_is_cancelled() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "an unpaid order is cancelled", steps: [
    tazuna.step_command(
      command: set_price(),
      caller: Staff,
      input: NewPrice(sku: "MUG", price: 1200),
    ),
    {
      use placed <- tazuna.step_command_then(
        command: place_order(),
        caller: Customer,
        input: NewOrder(
          email: "ann@example.com",
          lines: bag.from_list([shared.Line(sku: "MUG", quantity: 1)]),
        ),
      )
      let order = tazuna.fresh(placed, 0)
      [
        tazuna.step_event(
          source: shared.stock_events(),
          value: shared.StockHeld(order),
        ),
        tazuna.step_wait(for: duration.minutes(14)),
        tazuna.step_query(query: order_status(), caller: Customer, input: order),
        tazuna.step_wait(for: duration.minutes(1)),
        tazuna.step_query(query: order_status(), caller: Customer, input: order),
      ]
    },
  ])
}

/// How far prove, explore and search look in orders: three orders, as many
/// as can wait for payment at once, and two prices.
pub fn scope() -> tazuna.Scope {
  tazuna.scope(
    service: service(),
    creates: [
      tazuna.create(table: fn(records: Records) { records.orders }, at_most: 3),
      tazuna.create(table: fn(records: Records) { records.prices }, at_most: 2),
    ],
    others_at_most: 2,
    steps: 3,
    explore_depth: 6,
    explore_states: 10_000,
    waits: [],
    values: [
      tazuna.values(
        of: tazuna.declare_command(set_price()),
        ints: [0, 1],
        strings: ["", "MUG"],
      ),
      tazuna.values(
        of: tazuna.declare_command(place_order()),
        ints: [0, 1, 10, 11],
        strings: ["", "MUG"],
      ),
    ],
  )
}
