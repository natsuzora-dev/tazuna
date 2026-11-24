//// The tazuna DSL. Lean gives a spec its meaning, so the bodies here only
//// let a spec compile; Gleam never runs them.

import tazuna/internal/launch

/// What a spec's root module returns from `spec()`.
pub type Spec

/// `gleam run -m tazuna -- <command> <root> [...]` checks the spec whose
/// root module is `src/<root>.gleam`.
pub fn main() -> Nil {
  launch.main()
}
// Built-ins begin. `lake exe gen-dsl --write ..` in lean/ writes them; do not edit.
// Built-ins end.
