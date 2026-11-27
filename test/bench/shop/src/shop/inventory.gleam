//// Inventory: stock on hand per SKU. A placed order reserves all of its
//// lines or none; a cancelled order gives its reservation back; the
//// warehouse picks reserved orders. Staff hear when a SKU runs low.

import gleam/option.{type Option, None, Some}
import shop/shared.{
  type Caller, type Line, type OrderCancelled, type OrderPlaced, Staff,
  Warehouse,
}
import tazuna.{type Ctx, type Id, type MachineCtx, type QueryCtx}
import tazuna/bag.{type Bag}
import tazuna/table.{type Table}

/// Units on hand per SKU, and the lines each order holds.
pub type Records {
  Records(stock: Table(String, Int), reservations: Table(Id, Bag(Line)))
}

pub type Event {
  OrderArrived(placed: OrderPlaced)
  OrderWithdrawn(cancelled: OrderCancelled)
  Restocked(sku: String, quantity: Int)
  StockReserved(order: Id, lines: Bag(Line))
  StockRefused(order: Id, missing: Bag(String))
  DuplicateArrival(order: Id)
  StockReleased(order: Id, lines: Bag(Line))
  Picked(order: Id)
}

pub type Rejection {
  OutOfStock(missing: Bag(String))
  AlreadyReserved
  NotReserved
}

pub type Restock {
  Restock(sku: String, quantity: Int)
}

pub type ReserveRequest {
  ReserveRequest(order: Id, lines: Bag(Line))
}

pub type Level {
  Plenty
  Low
}

const low_mark: Int = 5

fn quantity(line: Line) -> Int {
  line.quantity
}

/// Units of the SKU across the lines, which may name it more than once.
fn wanted(lines: Bag(Line), sku: String) -> Int {
  bag.sum(
    bag.filter(lines, keeping: fn(line: Line) { line.sku == sku }),
    of: quantity,
  )
}

fn on_hand(records: Records, sku: String) -> Int {
  case table.get(records.stock, sku) {
    Some(units) -> units
    None -> 0
  }
}

fn take(stock: Table(String, Int), lines: Bag(Line)) -> Table(String, Int) {
  table.map(stock, with: fn(sku: String, units: Int) {
    units - wanted(lines, sku)
  })
}

fn give_back(
  stock: Table(String, Int),
  lines: Bag(Line),
) -> Table(String, Int) {
  table.map(stock, with: fn(sku: String, units: Int) {
    units + wanted(lines, sku)
  })
}

fn missing(records: Records, lines: Bag(Line)) -> Bag(String) {
  bag.map(
    bag.filter(lines, keeping: fn(line: Line) {
      on_hand(records, line.sku) < wanted(lines, line.sku)
    }),
    with: fn(line: Line) { line.sku },
  )
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    Restocked(sku, units) ->
      Records(
        ..records,
        stock: table.insert(records.stock, sku, on_hand(records, sku) + units),
      )
    StockReserved(order, lines) ->
      Records(
        stock: take(records.stock, lines),
        reservations: table.insert(records.reservations, order, lines),
      )
    StockReleased(order, lines) ->
      Records(
        stock: give_back(records.stock, lines),
        reservations: table.remove(records.reservations, order),
      )
    Picked(order) ->
      Records(
        ..records,
        reservations: table.remove(records.reservations, order),
      )
    OrderArrived(..)
    | OrderWithdrawn(..)
    | StockRefused(..)
    | DuplicateArrival(..) -> records
  }
}

pub fn restock() -> tazuna.Command(Records, Event, Caller, Restock, Rejection) {
  tazuna.command(
    name: "restock",
    callers: [tazuna.Outside(Staff), tazuna.Outside(Warehouse)],
    accepts: fn(input: Restock) {
      [
        #("sku is given", input.sku != ""),
        #("1 to 1000 units", input.quantity >= 1 && input.quantity <= 1000),
      ]
    },
    decide: fn(ctx: Ctx(Records, Restock, Caller)) {
      Ok([Restocked(ctx.input.sku, ctx.input.quantity)])
    },
    ensures: fn(ctx: Ctx(Records, Restock, Caller), after: Records) {
      [
        #(
          "the units are on hand",
          on_hand(after, ctx.input.sku)
            == on_hand(ctx.records, ctx.input.sku) + ctx.input.quantity,
        ),
      ]
    },
  )
}

/// Reserves every line of the order, or rejects with the SKUs short of stock.
pub fn reserve() -> tazuna.Command(
  Records,
  Event,
  Caller,
  ReserveRequest,
  Rejection,
) {
  tazuna.command(
    name: "reserve",
    callers: [tazuna.Own],
    accepts: fn(input: ReserveRequest) {
      [#("at least one line", bag.size(input.lines) >= 1)]
    },
    decide: fn(ctx: Ctx(Records, ReserveRequest, Caller)) {
      use <- tazuna.require(
        table.get(ctx.records.reservations, ctx.input.order) == None,
        or: AlreadyReserved,
      )
      let short = missing(ctx.records, ctx.input.lines)
      use <- tazuna.require(bag.size(short) == 0, or: OutOfStock(short))
      Ok([StockReserved(ctx.input.order, ctx.input.lines)])
    },
    ensures: fn(ctx: Ctx(Records, ReserveRequest, Caller), after: Records) {
      [
        #(
          "the order holds its lines",
          table.get(after.reservations, ctx.input.order)
            == Some(ctx.input.lines),
        ),
      ]
    },
  )
}

pub fn release() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "release",
    callers: [tazuna.Own],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use lines <- table.lookup(
        ctx.records.reservations,
        ctx.input,
        or: NotReserved,
      )
      Ok([StockReleased(ctx.input, lines)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #(
          "the reservation is gone",
          table.get(after.reservations, ctx.input) == None,
        ),
      ]
    },
  )
}

/// The warehouse takes a reserved order off the shelves to pack it.
pub fn pick() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "pick",
    callers: [tazuna.Outside(Warehouse)],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use _lines <- table.lookup(
        ctx.records.reservations,
        ctx.input,
        or: NotReserved,
      )
      Ok([Picked(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #(
          "the order no longer holds stock",
          table.get(after.reservations, ctx.input) == None,
        ),
      ]
    },
  )
}

pub fn stock_level() -> tazuna.Query(Records, Caller, String, Option(Int)) {
  tazuna.query(
    name: "stock level",
    callers: [tazuna.Outside(Staff), tazuna.Outside(Warehouse)],
    accepts: fn(_sku: String) { [] },
    resolve: fn(ctx: QueryCtx(Records, String, Caller)) {
      table.get(ctx.records.stock, ctx.input)
    },
  )
}

/// Reserves each arriving order and releases each withdrawn one.
fn allocate() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "allocate",
    react: fn(ctx: tazuna.ReactionCtx(Records), event: Event) {
      case event {
        OrderArrived(placed) -> [
          tazuna.send_command(
            command: reserve(),
            input: ReserveRequest(order: placed.order, lines: placed.lines),
            on_answer: fn(answer: Result(Nil, Rejection)) {
              case answer {
                Ok(Nil) -> []
                Error(OutOfStock(short)) -> [StockRefused(placed.order, short)]
                Error(AlreadyReserved) -> [DuplicateArrival(placed.order)]
                Error(NotReserved) -> []
              }
            },
          ),
        ]
        OrderWithdrawn(cancelled) ->
          case table.get(ctx.records.reservations, cancelled.order) {
            Some(_lines) -> [
              tazuna.send_command(
                command: release(),
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

/// One instance per SKU stocked: staff are mailed when it drops under the
/// low mark.
fn low_stock() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "low stock",
    instances: fn(records: Records) { table.keys(records.stock) },
    initial: Plenty,
    on: fn(ctx: MachineCtx(String, Level, Records), _event: Event) {
      let low = on_hand(ctx.records, ctx.key) < low_mark
      case ctx.state, low {
        Plenty, True -> tazuna.Enter(Low)
        Low, False -> tazuna.Enter(Plenty)
        _, _ -> tazuna.Stay
      }
    },
    timer: fn(_ctx: tazuna.TimerCtx(String, Level, Records)) { None },
    effect: fn(ctx: MachineCtx(String, Level, Records)) {
      case ctx.state {
        Plenty -> None
        Low ->
          Some(
            tazuna.request_command(
              command: shared.send_mail(),
              input: shared.Mail(
                to: "stock@shop.example",
                subject: "Low stock: " <> ctx.key,
                body: "Reorder " <> ctx.key <> " soon.",
              ),
              on_answer: fn(_answer: Result(Nil, shared.MailRefused)) { [] },
            ),
          )
      }
    },
    invariants: fn(ctx: MachineCtx(String, Level, Records)) {
      [
        #("low means under the mark", case ctx.state {
          Low -> on_hand(ctx.records, ctx.key) < low_mark
          Plenty -> True
        }),
      ]
    },
  )
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "inventory",
    init: Records(stock: table.new(), reservations: table.new()),
    apply: apply,
    subscribes: [
      tazuna.subscribe(to: shared.order_placed(), wrap: fn(placed: OrderPlaced) {
        OrderArrived(placed)
      }),
      tazuna.subscribe(
        to: shared.order_cancelled(),
        wrap: fn(cancelled: OrderCancelled) { OrderWithdrawn(cancelled) },
      ),
    ],
    declares: [
      tazuna.declare_command(restock()),
      tazuna.declare_command(reserve()),
      tazuna.declare_command(release()),
      tazuna.declare_command(pick()),
      tazuna.declare_query(stock_level()),
      tazuna.declare_source(shared.reservations()),
    ],
    machines: [low_stock()],
    reactions: [allocate()],
    invariants: fn(records: Records) {
      [
        #(
          "stock is never negative",
          table.all(records.stock, satisfying: fn(_sku, units: Int) {
            units >= 0
          }),
        ),
        #(
          "every reservation holds a line",
          table.all(
            records.reservations,
            satisfying: fn(_order, lines: Bag(Line)) { bag.size(lines) >= 1 },
          ),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "an arriving order is answered at once",
        after: fn(event: Event) {
          case event {
            OrderArrived(..) -> True
            _ -> False
          }
        },
        then: fn(trigger: Event, event: Event) {
          case trigger, event {
            OrderArrived(placed), StockReserved(order: reserved, ..) ->
              reserved == placed.order
            OrderArrived(placed), StockRefused(order: refused, ..) ->
              refused == placed.order
            OrderArrived(placed), DuplicateArrival(order: again) ->
              again == placed.order
            _, _ -> False
          }
        },
        within: 0,
        deadline: fn(_records: Records, _trigger: Event) { None },
      ),
    ],
    bounds: tazuna.bounds(
      creates: [
        tazuna.create(table: fn(records: Records) { records.stock }, at_most: 3),
        tazuna.create(
          table: fn(records: Records) { records.reservations },
          at_most: 3,
        ),
      ],
      items: 2,
      cascade: 2,
      steps: 4,
    ),
    scenarios: [restocking_adds_up()],
  )
}

/// A scenario cannot write an id that another service made, so no order
/// arrives here.
fn restocking_adds_up() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "restocking adds up", steps: [
    tazuna.step_command(
      command: restock(),
      caller: Staff,
      input: Restock(sku: "MUG-01", quantity: 3),
    ),
    tazuna.step_command(
      command: restock(),
      caller: Warehouse,
      input: Restock(sku: "MUG-01", quantity: 4),
    ),
    tazuna.step_query(query: stock_level(), caller: Warehouse, input: "MUG-01"),
  ])
}
