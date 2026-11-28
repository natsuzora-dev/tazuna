//// What the shop's services share: who calls them, the events one service
//// publishes for the others, and the externals they talk to.

import tazuna.{type Id}
import tazuna/bag.{type Bag}

/// Who sends a request from outside: a shopper on the storefront, a member
/// of staff in the back office, or the warehouse's packing station.
pub type Caller {
  Customer
  Staff
  Warehouse
}

/// One line of an order: so many units of a product at the price the
/// customer saw, in cents.
pub type Line {
  Line(sku: String, quantity: Int, unit_price: Int)
}

/// Orders publishes this once an order is placed.
pub type OrderPlaced {
  OrderPlaced(
    order: Id,
    customer: String,
    email: String,
    address: String,
    lines: Bag(Line),
    total: Int,
  )
}

/// Orders publishes this when an order is cancelled, by the customer or
/// because it was never paid or never reserved.
pub type OrderCancelled {
  OrderCancelled(order: Id, reason: String)
}

/// Inventory publishes the outcome of reserving an order's lines: all of
/// them, or none and the SKUs short of stock.
pub type Reservation {
  Reserved(order: Id)
  Unavailable(order: Id, missing: Bag(String))
}

/// Payments publishes the outcome of charging an order.
pub type PaymentOutcome {
  Captured(order: Id, amount: Int)
  Declined(order: Id, reason: String)
  Refunded(order: Id, amount: Int)
}

/// Shipping publishes how a parcel's journey ended.
pub type Delivery {
  Delivered(order: Id)
  Returned(order: Id)
}

/// Catalog publishes a product's new price.
pub type PriceChanged {
  PriceChanged(sku: String, price: Int)
}

pub fn order_placed() -> tazuna.Source(OrderPlaced) {
  tazuna.source(name: "order placed")
}

pub fn order_cancelled() -> tazuna.Source(OrderCancelled) {
  tazuna.source(name: "order cancelled")
}

pub fn reservations() -> tazuna.Source(Reservation) {
  tazuna.source(name: "reservation")
}

pub fn payment_outcomes() -> tazuna.Source(PaymentOutcome) {
  tazuna.source(name: "payment outcome")
}

pub fn deliveries() -> tazuna.Source(Delivery) {
  tazuna.source(name: "delivery")
}

pub fn price_changes() -> tazuna.Source(PriceChanged) {
  tazuna.source(name: "price changed")
}

/// What the mailer is asked to send.
pub type Mail {
  Mail(to: String, subject: String, body: String)
}

pub type MailRefused {
  BadAddress
  Throttled
}

pub fn send_mail() -> tazuna.ExternalCommand(Mail, Nil, MailRefused) {
  tazuna.external_command(name: "send")
}

/// A charge at the payment gateway, in cents; the order is the idempotency
/// key, so the gateway drops a retried charge it already took.
pub type Charge {
  Charge(order: Id, amount: Int, currency: String)
}

pub type Receipt {
  Receipt(transaction: String)
}

pub type ChargeRefused {
  CardDeclined(code: String)
  GatewayDown
}

pub type Refund {
  Refund(transaction: String, amount: Int)
}

/// The gateway's fraud score for a customer, from 0 (safe) to 100.
pub type RiskQuestion {
  RiskQuestion(customer: String, amount: Int)
}

pub fn charge() -> tazuna.ExternalCommand(Charge, Receipt, ChargeRefused) {
  tazuna.external_command(name: "charge")
}

pub fn refund() -> tazuna.ExternalCommand(Refund, Nil, ChargeRefused) {
  tazuna.external_command(name: "refund")
}

pub fn risk_score() -> tazuna.ExternalQuery(RiskQuestion, Int) {
  tazuna.external_query(
    name: "risk score",
    ensures: fn(_question: RiskQuestion, score: Int) {
      [#("score is 0 to 100", score >= 0 && score <= 100)]
    },
  )
}

/// A parcel the carrier is asked to collect.
pub type Parcel {
  Parcel(order: Id, address: String, items: Int)
}

pub type Label {
  Label(tracking: String)
}

pub type BookingRefused {
  Unserviceable
  CarrierBusy
}

/// The carrier's scans of a parcel as it travels.
pub type Scan {
  OutForDelivery(tracking: String)
  DeliveredTo(tracking: String)
  ReturnedToSender(tracking: String)
}

pub fn book_parcel() -> tazuna.ExternalCommand(Parcel, Label, BookingRefused) {
  tazuna.external_command(name: "book")
}

pub fn scans() -> tazuna.Source(Scan) {
  tazuna.source(name: "scan")
}
