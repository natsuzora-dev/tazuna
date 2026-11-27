//// Shipping: once an order is paid, shipping books a parcel with the
//// carrier and follows the carrier's scans. A parcel not delivered five
//// days after booking is reported late, and the customer hears about it.

import gleam/option.{type Option, None, Some}
import shop/shared.{
  type Caller, type Line, type OrderCancelled, type OrderPlaced,
  type PaymentOutcome, type Scan, Customer, Staff,
}
import tazuna.{
  type Ctx, type Id, type Instant, type MachineCtx, type QueryCtx, type TimerCtx,
}
import tazuna/bag
import tazuna/table.{type Table}

pub type ShipState {
  Pending
  Booking
  Stuck
  Booked
  OutForDelivery
  Delivered
  Returned
  Cancelled
}

pub type Shipment {
  Shipment(
    email: String,
    address: String,
    items: Int,
    state: ShipState,
    tracking: Option(String),
    late_at: Instant,
    reported_late: Bool,
  )
}

pub type Records {
  Records(shipments: Table(Id, Shipment))
}

pub type Event {
  Expected(placed: OrderPlaced)
  PaymentNews(outcome: PaymentOutcome)
  CalledOff(cancelled: OrderCancelled)
  Scanned(scan: Scan)
  LabelIssued(order: Id, tracking: String)
  BookingFailed(order: Id, reason: String)
  AddressChanged(order: Id, address: String)
  Rebooked(order: Id)
  ParcelLate(order: Id)
}

pub type Rejection {
  UnknownShipment
  AlreadyBooked
  NotStuck
  NotInTransit
}

pub type AddressChange {
  AddressChange(order: Id, address: String)
}

pub type Booking {
  Requesting
}

pub type Transit {
  InTransit
  Late
}

fn quantity(line: Line) -> Int {
  line.quantity
}

fn state_of(records: Records, order: Id) -> Option(ShipState) {
  case table.get(records.shipments, order) {
    Some(shipment) -> Some(shipment.state)
    None -> None
  }
}

fn change(
  records: Records,
  order: Id,
  when: fn(ShipState) -> Bool,
  to: fn(Shipment) -> Shipment,
) -> Records {
  case table.get(records.shipments, order) {
    Some(shipment) ->
      case when(shipment.state) {
        True ->
          Records(shipments: table.insert(
            records.shipments,
            order,
            to(shipment),
          ))
        False -> records
      }
    None -> records
  }
}

fn into(state: ShipState) -> fn(Shipment) -> Shipment {
  fn(shipment: Shipment) { Shipment(..shipment, state: state) }
}

/// Moves every parcel with the tracking number from one state to another.
fn scanned(
  records: Records,
  tracking: String,
  from: fn(ShipState) -> Bool,
  to: ShipState,
) -> Records {
  Records(
    shipments: table.map(
      records.shipments,
      with: fn(_order: Id, shipment: Shipment) {
        case shipment.tracking == Some(tracking) && from(shipment.state) {
          True -> Shipment(..shipment, state: to)
          False -> shipment
        }
      },
    ),
  )
}

fn not_yet_booked(state: ShipState) -> Bool {
  state == Pending || state == Booking || state == Stuck
}

fn travelling(state: ShipState) -> Bool {
  state == Booked || state == OutForDelivery
}

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    Expected(placed) ->
      case table.get(records.shipments, placed.order) {
        Some(_) -> records
        None ->
          Records(shipments: table.insert(
            records.shipments,
            placed.order,
            Shipment(
              email: placed.email,
              address: placed.address,
              items: bag.sum(placed.lines, of: quantity),
              state: Pending,
              tracking: None,
              late_at: ctx.now,
              reported_late: False,
            ),
          ))
      }
    PaymentNews(shared.Captured(order, _amount)) ->
      change(records, order, fn(state) { state == Pending }, into(Booking))
    PaymentNews(_) -> records
    CalledOff(cancelled) ->
      change(records, cancelled.order, not_yet_booked, into(Cancelled))
    Scanned(shared.OutForDelivery(tracking)) ->
      scanned(records, tracking, fn(state) { state == Booked }, OutForDelivery)
    Scanned(shared.DeliveredTo(tracking)) ->
      scanned(records, tracking, travelling, Delivered)
    Scanned(shared.ReturnedToSender(tracking)) ->
      scanned(records, tracking, travelling, Returned)
    LabelIssued(order, tracking) ->
      change(
        records,
        order,
        fn(state) { state == Booking },
        fn(shipment: Shipment) {
          Shipment(
            ..shipment,
            state: Booked,
            tracking: Some(tracking),
            late_at: ctx.now + 5 * shared.day,
          )
        },
      )
    BookingFailed(order, _reason) ->
      change(records, order, fn(state) { state == Booking }, into(Stuck))
    AddressChanged(order, address) ->
      change(records, order, not_yet_booked, fn(shipment: Shipment) {
        Shipment(..shipment, address: address)
      })
    Rebooked(order) ->
      change(records, order, fn(state) { state == Stuck }, into(Booking))
    ParcelLate(order) ->
      change(records, order, travelling, fn(shipment: Shipment) {
        Shipment(..shipment, reported_late: True)
      })
  }
}

pub fn change_address() -> tazuna.Command(
  Records,
  Event,
  Caller,
  AddressChange,
  Rejection,
) {
  tazuna.command(
    name: "change address",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(input: AddressChange) {
      [#("address is given", input.address != "")]
    },
    decide: fn(ctx: Ctx(Records, AddressChange, Caller)) {
      use shipment <- table.lookup(
        ctx.records.shipments,
        ctx.input.order,
        or: UnknownShipment,
      )
      use <- tazuna.require(
        shipment.state == Pending || shipment.state == Stuck,
        or: AlreadyBooked,
      )
      Ok([AddressChanged(ctx.input.order, ctx.input.address)])
    },
    ensures: fn(ctx: Ctx(Records, AddressChange, Caller), after: Records) {
      [
        #(
          "the parcel goes to the new address",
          case table.get(after.shipments, ctx.input.order) {
            Some(shipment) -> shipment.address == ctx.input.address
            None -> False
          },
        ),
      ]
    },
  )
}

/// Staff book a stuck parcel again, usually after fixing its address.
pub fn rebook() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "rebook",
    callers: [tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use shipment <- table.lookup(
        ctx.records.shipments,
        ctx.input,
        or: UnknownShipment,
      )
      use <- tazuna.require(shipment.state == Stuck, or: NotStuck)
      Ok([Rebooked(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #(
          "the parcel is booked again",
          state_of(after, ctx.input) == Some(Booking),
        ),
      ]
    },
  )
}

pub fn report_late() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "report late",
    callers: [tazuna.Own],
    accepts: fn(_order: Id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use shipment <- table.lookup(
        ctx.records.shipments,
        ctx.input,
        or: UnknownShipment,
      )
      use <- tazuna.require(travelling(shipment.state), or: NotInTransit)
      Ok([ParcelLate(ctx.input)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

pub fn tracking() -> tazuna.Query(Records, Caller, Id, Option(String)) {
  tazuna.query(
    name: "tracking",
    callers: [tazuna.Outside(Customer), tazuna.Outside(Staff)],
    accepts: fn(_order: Id) { [] },
    resolve: fn(ctx: QueryCtx(Records, Id, Caller)) {
      case table.get(ctx.records.shipments, ctx.input) {
        Some(shipment) -> shipment.tracking
        None -> None
      }
    },
  )
}

/// One instance per parcel being booked: it asks the carrier for a label.
fn booking() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "booking",
    instances: fn(records: Records) {
      table.keys(
        table.filter(records.shipments, keeping: fn(_order, shipment: Shipment) {
          shipment.state == Booking
        }),
      )
    },
    initial: Requesting,
    on: fn(_ctx: MachineCtx(Id, Booking, Records), _event: Event) {
      tazuna.Stay
    },
    timer: fn(_ctx: TimerCtx(Id, Booking, Records)) { None },
    effect: fn(ctx: MachineCtx(Id, Booking, Records)) {
      let order = ctx.key
      case table.get(ctx.records.shipments, order) {
        Some(shipment) ->
          Some(
            tazuna.request_command(
              command: shared.book_parcel(),
              input: shared.Parcel(
                order: order,
                address: shipment.address,
                items: shipment.items,
              ),
              on_answer: fn(answer: Result(shared.Label, shared.BookingRefused)) {
                case answer {
                  Ok(label) -> [LabelIssued(order, label.tracking)]
                  Error(shared.Unserviceable) -> [
                    BookingFailed(order, "address not served"),
                  ]
                  Error(shared.CarrierBusy) -> [
                    BookingFailed(order, "carrier busy"),
                  ]
                }
              },
            ),
          )
        None -> None
      }
    },
    invariants: fn(_ctx: MachineCtx(Id, Booking, Records)) { [] },
  )
}

/// One instance per parcel on its way: at its late-at time, five days after
/// booking, it is late.
fn delivery_watch() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "delivery watch",
    instances: fn(records: Records) {
      table.keys(
        table.filter(records.shipments, keeping: fn(_order, shipment: Shipment) {
          travelling(shipment.state)
        }),
      )
    },
    initial: InTransit,
    on: fn(_ctx: MachineCtx(Id, Transit, Records), _event: Event) {
      tazuna.Stay
    },
    timer: fn(ctx: TimerCtx(Id, Transit, Records)) {
      case ctx.state, table.get(ctx.records.shipments, ctx.key) {
        InTransit, Some(shipment) ->
          Some(tazuna.Timer(at: shipment.late_at, enter: Late))
        _, _ -> None
      }
    },
    effect: fn(ctx: MachineCtx(Id, Transit, Records)) {
      case ctx.state {
        InTransit -> None
        Late ->
          Some(
            tazuna.send_command(
              command: report_late(),
              input: ctx.key,
              on_answer: fn(_answer: Result(Nil, Rejection)) { [] },
            ),
          )
      }
    },
    invariants: fn(ctx: MachineCtx(Id, Transit, Records)) {
      [
        #(
          "a parcel on its way has a tracking number",
          case table.get(ctx.records.shipments, ctx.key) {
            Some(shipment) -> shipment.tracking != None
            None -> False
          },
        ),
        #(
          "a late parcel is reported",
          case ctx.state, table.get(ctx.records.shipments, ctx.key) {
            Late, Some(shipment) -> shipment.reported_late
            _, _ -> True
          },
        ),
      ]
    },
  )
}

/// Tells the customer their parcel is late.
fn apologise() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "apologise",
    react: fn(ctx: tazuna.ReactionCtx(Records), event: Event) {
      case event {
        ParcelLate(order) ->
          case table.get(ctx.records.shipments, order) {
            Some(shipment) -> [
              tazuna.request_command(
                command: shared.send_mail(),
                input: shared.Mail(
                  to: shipment.email,
                  subject: "Your parcel is late",
                  body: "We are sorry: your parcel to "
                    <> shipment.address
                    <> " is taking longer than planned.",
                ),
                on_answer: fn(_answer: Result(Nil, shared.MailRefused)) { [] },
              ),
            ]
            None -> []
          }
        _ -> []
      }
    },
  )
}

pub fn service() -> tazuna.Service {
  tazuna.service(
    name: "shipping",
    init: Records(shipments: table.new()),
    apply: apply,
    subscribes: [
      tazuna.subscribe(to: shared.order_placed(), wrap: fn(placed: OrderPlaced) {
        Expected(placed)
      }),
      tazuna.subscribe(
        to: shared.payment_outcomes(),
        wrap: fn(outcome: PaymentOutcome) { PaymentNews(outcome) },
      ),
      tazuna.subscribe(
        to: shared.order_cancelled(),
        wrap: fn(cancelled: OrderCancelled) { CalledOff(cancelled) },
      ),
      tazuna.subscribe(to: shared.scans(), wrap: fn(scan: Scan) {
        Scanned(scan)
      }),
    ],
    declares: [
      tazuna.declare_command(change_address()),
      tazuna.declare_command(rebook()),
      tazuna.declare_command(report_late()),
      tazuna.declare_query(tracking()),
      tazuna.declare_source(shared.deliveries()),
    ],
    machines: [booking(), delivery_watch()],
    reactions: [apologise()],
    invariants: fn(records: Records) {
      [
        #(
          "every parcel has an address",
          table.all(
            records.shipments,
            satisfying: fn(_order, shipment: Shipment) {
              shipment.address != ""
            },
          ),
        ),
        #(
          "every parcel holds an item",
          table.all(
            records.shipments,
            satisfying: fn(_order, shipment: Shipment) { shipment.items >= 1 },
          ),
        ),
        #(
          "a booked parcel has a tracking number",
          table.all(
            records.shipments,
            satisfying: fn(_order, shipment: Shipment) {
              case shipment.state {
                Booked | OutForDelivery | Delivered | Returned ->
                  shipment.tracking != None
                _ -> True
              }
            },
          ),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "a booked parcel arrives, returns or is late within 5 days",
        after: fn(event: Event) {
          case event {
            LabelIssued(..) -> True
            _ -> False
          }
        },
        then: fn(trigger: Event, event: Event) {
          case trigger, event {
            LabelIssued(tracking:, ..), Scanned(shared.DeliveredTo(scanned)) ->
              scanned == tracking
            LabelIssued(tracking:, ..),
              Scanned(shared.ReturnedToSender(scanned))
            -> scanned == tracking
            LabelIssued(order:, ..), ParcelLate(late) -> late == order
            _, _ -> False
          }
        },
        within: 5 * shared.day,
        deadline: fn(records: Records, trigger: Event) {
          case trigger {
            LabelIssued(order:, tracking:) ->
              case table.get(records.shipments, order) {
                Some(shipment) ->
                  case
                    travelling(shipment.state)
                    && shipment.tracking == Some(tracking)
                    && !shipment.reported_late
                  {
                    True -> Some(shipment.late_at)
                    False -> None
                  }
                None -> None
              }
            _ -> None
          }
        },
      ),
    ],
    bounds: tazuna.bounds(
      creates: [
        tazuna.create(
          table: fn(records: Records) { records.shipments },
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
