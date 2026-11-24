import tazuna

// No built-in builds a Spec yet, so the root cannot have the type Lean asks
// for, and Lean refuses the converted IR.
pub fn spec(s: tazuna.Spec) -> tazuna.Spec {
  s
}
