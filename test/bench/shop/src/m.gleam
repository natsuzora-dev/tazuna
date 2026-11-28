//// An online shop of five services and the three externals they call.

import shop/catalog
import shop/inventory
import shop/orders
import shop/payments
import shop/shared
import shop/shipping
import tazuna

pub fn spec() -> tazuna.Spec {
  tazuna.spec(
    services: [
      catalog.service(),
      orders.service(),
      inventory.service(),
      payments.service(),
      shipping.service(),
    ],
    externals: [
      tazuna.external(name: "mailer", declares: [
        tazuna.declare_external_command(shared.send_mail()),
      ]),
      tazuna.external(name: "payment gateway", declares: [
        tazuna.declare_external_command(shared.charge()),
        tazuna.declare_external_command(shared.refund()),
        tazuna.declare_external_query(shared.risk_score()),
      ]),
      tazuna.external(name: "carrier", declares: [
        tazuna.declare_external_command(shared.book_parcel()),
        tazuna.declare_source(shared.scans()),
      ]),
    ],
  )
}

/// The model a commit is checked in. explore looks 6 inputs deep, one past the
/// longest life of a record here (a parcel: ordered, paid, labelled, scanned,
/// then late). Its value sets are the values on both sides of each bound the
/// spec writes, and each service's state cap is about 1.2 million transitions
/// over the inputs a state tries with those values, so explore's share of the
/// run is about 6 million transitions.
pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    catalog.scope(),
    orders.scope(),
    inventory.scope(),
    payments.scope(),
    shipping.scope(),
  ])
}
