//// The catalog: the products the shop sells, their prices, and day-long
//// sales. Staff edit it; everyone reads prices from it.

import gleam/option.{type Option, None, Some}
import shop/shared.{type Caller, Customer, Staff}
import tazuna.{
  type Ctx, type Instant, type MachineCtx, type QueryCtx, type TimerCtx,
}
import tazuna/table.{type Table}

pub type Product {
  Product(name: String, price: Int, active: Bool)
}

/// A sale: the percentage off, and when it ends.
pub type Sale {
  Sale(percent: Int, ends: Instant)
}

/// Products by SKU, and the sales by SKU.
pub type Records {
  Records(products: Table(String, Product), sales: Table(String, Sale))
}

pub type Event {
  ProductAdded(sku: String, name: String, price: Int)
  PriceSet(sku: String, price: Int)
  ProductRetired(sku: String)
  SaleStarted(sku: String, percent: Int)
  SaleEnded(sku: String)
}

pub type Rejection {
  DuplicateSku
  UnknownSku
  Retired
  AlreadyOnSale
  StillOnSale
  NotOnSale
}

pub type NewProduct {
  NewProduct(sku: String, name: String, price: Int)
}

pub type PriceChange {
  PriceChange(sku: String, price: Int)
}

pub type SaleStart {
  SaleStart(sku: String, percent: Int)
}

pub type SalePhase {
  Running
  Over
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    ProductAdded(sku, name, price) ->
      Records(
        ..records,
        products: table.insert(
          records.products,
          sku,
          Product(name: name, price: price, active: True),
        ),
      )
    PriceSet(sku, price) ->
      case table.get(records.products, sku) {
        Some(product) ->
          Records(
            ..records,
            products: table.insert(
              records.products,
              sku,
              Product(..product, price: price),
            ),
          )
        None -> records
      }
    ProductRetired(sku) ->
      case table.get(records.products, sku) {
        Some(product) ->
          Records(
            ..records,
            products: table.insert(
              records.products,
              sku,
              Product(..product, active: False),
            ),
          )
        None -> records
      }
    SaleStarted(sku, percent) ->
      Records(
        ..records,
        sales: table.insert(
          records.sales,
          sku,
          Sale(percent: percent, ends: ctx.now + shared.day),
        ),
      )
    SaleEnded(sku) ->
      Records(..records, sales: table.remove(records.sales, sku))
  }
}

fn valid_sku(sku: String) -> Bool {
  tazuna.length(sku) >= 3 && tazuna.length(sku) <= 12
}

pub fn add_product() -> tazuna.Command(
  Records,
  Event,
  Caller,
  NewProduct,
  Rejection,
) {
  tazuna.command(
    name: "add product",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(input: NewProduct) {
      [
        #("sku has 3 to 12 characters", valid_sku(input.sku)),
        #("name is not empty", input.name != ""),
        #("price is positive", input.price > 0),
      ]
    },
    decide: fn(ctx: Ctx(Records, NewProduct, Caller)) {
      use <- tazuna.require(
        table.get(ctx.records.products, ctx.input.sku) == None,
        or: DuplicateSku,
      )
      Ok([ProductAdded(ctx.input.sku, ctx.input.name, ctx.input.price)])
    },
    ensures: fn(ctx: Ctx(Records, NewProduct, Caller), after: Records) {
      [
        #(
          "the product is on sale at its price",
          table.get(after.products, ctx.input.sku)
            == Some(Product(
            name: ctx.input.name,
            price: ctx.input.price,
            active: True,
          )),
        ),
      ]
    },
  )
}

pub fn change_price() -> tazuna.Command(
  Records,
  Event,
  Caller,
  PriceChange,
  Rejection,
) {
  tazuna.command(
    name: "change price",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(input: PriceChange) {
      [#("price is positive", input.price > 0)]
    },
    decide: fn(ctx: Ctx(Records, PriceChange, Caller)) {
      use product <- table.lookup(
        ctx.records.products,
        ctx.input.sku,
        or: UnknownSku,
      )
      use <- tazuna.require(product.active, or: Retired)
      Ok([PriceSet(ctx.input.sku, ctx.input.price)])
    },
    ensures: fn(ctx: Ctx(Records, PriceChange, Caller), after: Records) {
      [
        #("the new price holds", case table.get(after.products, ctx.input.sku) {
          Some(product) -> product.price == ctx.input.price
          None -> False
        }),
      ]
    },
  )
}

pub fn retire_product() -> tazuna.Command(
  Records,
  Event,
  Caller,
  String,
  Rejection,
) {
  tazuna.command(
    name: "retire product",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(_sku: String) { [] },
    decide: fn(ctx: Ctx(Records, String, Caller)) {
      use product <- table.lookup(
        ctx.records.products,
        ctx.input,
        or: UnknownSku,
      )
      use <- tazuna.require(product.active, or: Retired)
      use <- tazuna.require(
        table.get(ctx.records.sales, ctx.input) == None,
        or: StillOnSale,
      )
      Ok([ProductRetired(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, String, Caller), after: Records) {
      [
        #(
          "the product is no longer sold",
          case table.get(after.products, ctx.input) {
            Some(product) -> !product.active
            None -> False
          },
        ),
      ]
    },
  )
}

pub fn start_sale() -> tazuna.Command(
  Records,
  Event,
  Caller,
  SaleStart,
  Rejection,
) {
  tazuna.command(
    name: "start sale",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(input: SaleStart) {
      [
        #(
          "between 1 and 90 percent off",
          input.percent >= 1 && input.percent <= 90,
        ),
      ]
    },
    decide: fn(ctx: Ctx(Records, SaleStart, Caller)) {
      use product <- table.lookup(
        ctx.records.products,
        ctx.input.sku,
        or: UnknownSku,
      )
      use <- tazuna.require(product.active, or: Retired)
      use <- tazuna.require(
        table.get(ctx.records.sales, ctx.input.sku) == None,
        or: AlreadyOnSale,
      )
      Ok([SaleStarted(ctx.input.sku, ctx.input.percent)])
    },
    ensures: fn(ctx: Ctx(Records, SaleStart, Caller), after: Records) {
      [
        #("the sale runs", case table.get(after.sales, ctx.input.sku) {
          Some(sale) -> sale.percent == ctx.input.percent
          None -> False
        }),
      ]
    },
  )
}

pub fn end_sale() -> tazuna.Command(Records, Event, Caller, String, Rejection) {
  tazuna.command(
    name: "end sale",
    callers: [tazuna.Own],
    accepts: fn(_sku: String) { [] },
    decide: fn(ctx: Ctx(Records, String, Caller)) {
      use _sale <- table.lookup(ctx.records.sales, ctx.input, or: NotOnSale)
      Ok([SaleEnded(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, String, Caller), after: Records) {
      [#("the sale is over", table.get(after.sales, ctx.input) == None)]
    },
  )
}

/// The price a customer pays today, in cents, for a product still sold.
pub fn price_of() -> tazuna.Query(Records, Caller, String, Option(Int)) {
  tazuna.query(
    name: "price of",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(_sku: String) { [] },
    resolve: fn(ctx: QueryCtx(Records, String, Caller)) {
      case table.get(ctx.records.products, ctx.input) {
        Some(product) if product.active ->
          case table.get(ctx.records.sales, ctx.input) {
            Some(sale) -> Some(product.price * { 100 - sale.percent } / 100)
            None -> Some(product.price)
          }
        _ -> None
      }
    },
  )
}

/// Each sale runs until it ends, a day after it starts, then ends itself.
fn sale_clock() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "sale clock",
    instances: fn(records: Records) { table.keys(records.sales) },
    initial: Running,
    on: fn(_ctx: MachineCtx(String, SalePhase, Records), _event: Event) {
      tazuna.Stay
    },
    timer: fn(ctx: TimerCtx(String, SalePhase, Records)) {
      case ctx.state, table.get(ctx.records.sales, ctx.key) {
        Running, Some(sale) -> Some(tazuna.Timer(at: sale.ends, enter: Over))
        _, _ -> None
      }
    },
    effect: fn(ctx: MachineCtx(String, SalePhase, Records)) {
      case ctx.state {
        Running -> None
        Over ->
          Some(
            tazuna.send_command(
              command: end_sale(),
              input: ctx.key,
              on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
            ),
          )
      }
    },
    invariants: fn(ctx: MachineCtx(String, SalePhase, Records)) {
      [
        #(
          "a running sale's product is sold",
          case table.get(ctx.records.products, ctx.key) {
            Some(product) -> product.active
            None -> False
          },
        ),
      ]
    },
  )
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "catalog",
    init: Records(products: table.new(), sales: table.new()),
    apply: apply,
    subscribes: [],
    declares: [
      tazuna.declare_command(add_product()),
      tazuna.declare_command(change_price()),
      tazuna.declare_command(retire_product()),
      tazuna.declare_command(start_sale()),
      tazuna.declare_command(end_sale()),
      tazuna.declare_query(price_of()),
      tazuna.declare_source(shared.price_changes()),
    ],
    machines: [sale_clock()],
    reactions: [],
    invariants: fn(records: Records) {
      [
        #(
          "every price is positive",
          table.all(records.products, satisfying: fn(_sku, product: Product) {
            product.price > 0
          }),
        ),
        #(
          "every product has a name",
          table.all(records.products, satisfying: fn(_sku, product: Product) {
            product.name != ""
          }),
        ),
        #(
          "every sale is 1 to 90 percent off",
          table.all(records.sales, satisfying: fn(_sku, sale: Sale) {
            sale.percent >= 1 && sale.percent <= 90
          }),
        ),
        #(
          "every sale is of a product sold",
          table.all(records.sales, satisfying: fn(sku: String, _sale) {
            case table.get(records.products, sku) {
              Some(product) -> product.active
              None -> False
            }
          }),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "a sale ends within a day",
        after: fn(event: Event) {
          case event {
            SaleStarted(..) -> True
            _ -> False
          }
        },
        then: fn(trigger: Event, event: Event) {
          case trigger, event {
            SaleStarted(sku: started, ..), SaleEnded(sku: ended) ->
              started == ended
            _, _ -> False
          }
        },
        within: shared.day,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [
        tazuna.create(
          table: fn(records: Records) { records.products },
          at_most: 3,
        ),
        tazuna.create(table: fn(records: Records) { records.sales }, at_most: 2),
      ],
      items: 2,
      cascade: 1,
      steps: 4,
    ),
    scenarios: [a_sale_runs_for_a_day()],
  )
}

fn a_sale_runs_for_a_day() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "a sale runs for a day", steps: [
    tazuna.step_command(
      command: add_product(),
      caller: Staff,
      input: NewProduct(sku: "MUG-01", name: "Stoneware mug", price: 1800),
    ),
    tazuna.step_command(
      command: start_sale(),
      caller: Staff,
      input: SaleStart(sku: "MUG-01", percent: 25),
    ),
    tazuna.step_query(query: price_of(), caller: Customer, input: "MUG-01"),
    tazuna.step_command(
      command: retire_product(),
      caller: Staff,
      input: "MUG-01",
    ),
    tazuna.step_wait(for: shared.day),
    tazuna.step_query(query: price_of(), caller: Customer, input: "MUG-01"),
  ])
}
