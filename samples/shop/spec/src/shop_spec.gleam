//// A small online shop: orders runs the checkout, inventory holds stock,
//// and payments charges customers at the payment gateway.

import shop_spec/inventory
import shop_spec/orders
import shop_spec/payments
import tazuna

pub fn spec() -> tazuna.Spec {
  tazuna.spec(
    services: [orders.service(), inventory.service(), payments.service()],
    externals: [
      tazuna.external(name: "mailer", declares: [
        tazuna.declare_external_command(orders.send_mail()),
      ]),
      tazuna.external(name: "payment gateway", declares: [
        tazuna.declare_external_command(payments.charge()),
        tazuna.declare_external_command(payments.refund()),
      ]),
    ],
  )
}

/// The model each commit is checked in.
pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    orders.scope(),
    inventory.scope(),
    payments.scope(),
  ])
}
