//// Inventory: staff restock products, and inventory holds stock for orders.
////
//// When orders publishes `OrderPlaced`, inventory holds every line of the
//// order or none of them. A confirmed order's held stock is sold; a
//// cancelled order's goes back on the shelf.

import gleam/option.{None, Some}
import shop_spec/shared.{
  type Caller, type Line, type OrderEvent, Customer, Staff,
}
import tazuna.{type Ctx, type Id, type QueryCtx}
import tazuna/bag.{type Bag}
import tazuna/table.{type Table}

/// Units on the shelf by SKU, and the lines held for each open order.
pub type Records {
  Records(stock: Table(String, Int), holds: Table(Id, Bag(Line)))
}

pub type Event {
  Restocked(sku: String, units: Int)
  Held(order: Id, lines: Bag(Line))
  Unavailable(order: Id)
  OrderNews(news: OrderEvent)
}

pub type Rejection {
  AlreadyHeld
  QuantityNotPositive
}

pub type Delivery {
  Delivery(sku: String, units: Int)
}

pub type Hold {
  Hold(order: Id, lines: Bag(Line))
}

fn units_of(stock: Table(String, Int), sku: String) -> Int {
  case table.get(stock, sku) {
    Some(units) -> units
    None -> 0
  }
}

/// The units of `sku` that the lines ask for in all.
fn wanted(lines: Bag(Line), sku: String) -> Int {
  lines
  |> bag.filter(keeping: fn(line: Line) { line.sku == sku })
  |> bag.sum(of: fn(line: Line) { line.quantity })
}

/// The stock with the lines' units taken off the shelf (`sign` -1) or put
/// back (`sign` 1). Inventory holds only SKUs it stocks, so every SKU of a
/// hold is already in the table.
fn shift(
  stock: Table(String, Int),
  lines: Bag(Line),
  sign: Int,
) -> Table(String, Int) {
  table.map(stock, with: fn(sku, units) { units + sign * wanted(lines, sku) })
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    Restocked(sku, units) ->
      Records(
        ..records,
        stock: table.insert(
          records.stock,
          sku,
          units_of(records.stock, sku) + units,
        ),
      )
    Held(order, lines) ->
      Records(
        stock: shift(records.stock, lines, -1),
        holds: table.insert(records.holds, order, lines),
      )
    Unavailable(_) -> records
    OrderNews(shared.OrderCancelled(order)) ->
      case table.get(records.holds, order) {
        Some(lines) ->
          Records(
            stock: shift(records.stock, lines, 1),
            holds: table.remove(records.holds, order),
          )
        None -> records
      }
    OrderNews(shared.OrderConfirmed(order)) ->
      Records(..records, holds: table.remove(records.holds, order))
    OrderNews(_) -> records
  }
}

fn restock() -> tazuna.Command(Records, Event, Caller, Delivery, Rejection) {
  tazuna.command(
    name: "restock",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(input: Delivery) {
      [
        #("sku is given", input.sku != ""),
        #("units is positive", input.units > 0),
      ]
    },
    decide: fn(ctx: Ctx(Records, Delivery, Caller)) {
      Ok([Restocked(ctx.input.sku, ctx.input.units)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

/// Holds every line of an order, or reports that some product is short.
fn hold() -> tazuna.Command(Records, Event, Caller, Hold, Rejection) {
  tazuna.command(
    name: "hold",
    callers: [tazuna.Own],
    accepts: fn(_input) { [] },
    decide: fn(ctx: Ctx(Records, Hold, Caller)) {
      let Hold(order, lines) = ctx.input
      let stock = ctx.records.stock
      use <- tazuna.require(
        table.get(ctx.records.holds, order) == None,
        or: AlreadyHeld,
      )
      use <- tazuna.require(
        bag.all(lines, satisfying: fn(line: Line) { line.quantity > 0 }),
        or: QuantityNotPositive,
      )
      case
        bag.all(lines, satisfying: fn(line: Line) {
          table.get(stock, line.sku) != None
          && wanted(lines, line.sku) <= units_of(stock, line.sku)
        })
      {
        True -> Ok([Held(order, lines)])
        False -> Ok([Unavailable(order)])
      }
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

fn stock_level() -> tazuna.Query(Records, Caller, String, Int) {
  tazuna.query(
    name: "stock level",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(_sku) { [] },
    resolve: fn(ctx: QueryCtx(Records, String, Caller)) {
      units_of(ctx.records.stock, ctx.input)
    },
  )
}

/// Tries to hold the lines of each order placed.
fn holding() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(name: "holding", react: fn(_ctx, event) {
    case event {
      OrderNews(shared.OrderPlaced(order, lines)) -> [
        tazuna.send_command(
          command: hold(),
          input: Hold(order, lines),
          on_answer: fn(_answer) { [] },
        ),
      ]
      _ -> []
    }
  })
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "inventory",
    init: Records(stock: table.new(), holds: table.new()),
    apply: apply,
    subscribes: [tazuna.subscribe(to: shared.order_events(), wrap: OrderNews)],
    declares: [
      tazuna.declare_command(restock()),
      tazuna.declare_command(hold()),
      tazuna.declare_query(stock_level()),
      tazuna.declare_source(shared.stock_events()),
    ],
    machines: [],
    reactions: [holding()],
    invariants: fn(records: Records) {
      [
        #(
          "no stock level is negative",
          table.all(records.stock, satisfying: fn(_sku, units) { units >= 0 }),
        ),
        #(
          "every held quantity is positive",
          table.all(records.holds, satisfying: fn(_order, lines) {
            bag.all(lines, satisfying: fn(line: Line) { line.quantity > 0 })
          }),
        ),
      ]
    },
    responses: [],
    cascade: 1,
    scenarios: [],
  )
}

/// How far prove, explore and search look in inventory.
pub fn scope() -> tazuna.Scope {
  tazuna.scope(
    service: service(),
    creates: [
      tazuna.create(table: fn(records: Records) { records.stock }, at_most: 2),
      tazuna.create(table: fn(records: Records) { records.holds }, at_most: 2),
    ],
    others_at_most: 2,
    steps: 3,
    explore_depth: 6,
    explore_states: 10_000,
    waits: [],
    values: [
      tazuna.values(
        of: tazuna.declare_command(restock()),
        ints: [0, 1],
        strings: ["", "MUG"],
      ),
      tazuna.values(of: tazuna.declare_query(stock_level()), ints: [], strings: [
        "",
        "MUG",
      ]),
      tazuna.values(
        of: tazuna.declare_source(shared.order_events()),
        ints: [0, 1],
        strings: ["", "MUG"],
      ),
    ],
  )
}
