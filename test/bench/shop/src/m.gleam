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
