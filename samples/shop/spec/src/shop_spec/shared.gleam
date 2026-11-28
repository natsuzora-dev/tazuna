//// What the shop's services share: who calls them, an order line, and the
//// events each service publishes for the others.
////
//// Orders runs the checkout. It asks inventory to hold stock by publishing
//// `OrderPlaced`, asks payments to charge the customer by publishing
//// `PaymentDue`, and learns the outcome of each from their events.

import tazuna.{type Id}
import tazuna/bag.{type Bag}

/// Who sends a request from outside: a shopper, or a member of staff.
pub type Caller {
  Customer
  Staff
}

/// So many units of one product, named by its SKU.
pub type Line {
  Line(sku: String, quantity: Int)
}

/// What orders publishes about an order.
pub type OrderEvent {
  /// Hold these lines for the order.
  OrderPlaced(order: Id, lines: Bag(Line))
  /// The stock is held; charge the customer this many cents.
  PaymentDue(order: Id, amount: Int)
  /// The order is paid, so its held stock is sold.
  OrderConfirmed(order: Id)
  /// The order will not go ahead: release its stock and return its money.
  OrderCancelled(order: Id)
}

/// What inventory publishes after it tries to hold an order's lines.
pub type StockEvent {
  StockHeld(order: Id)
  OutOfStock(order: Id)
}

/// What payments publishes about the charge for an order.
pub type PaymentEvent {
  PaymentCaptured(order: Id)
  PaymentFailed(order: Id)
}

pub fn order_events() -> tazuna.Source(OrderEvent) {
  tazuna.source(name: "order")
}

pub fn stock_events() -> tazuna.Source(StockEvent) {
  tazuna.source(name: "stock")
}

pub fn payment_events() -> tazuna.Source(PaymentEvent) {
  tazuna.source(name: "payment")
}
