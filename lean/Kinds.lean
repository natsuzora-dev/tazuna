import Tazuna.Cli.Kind

/-- Prints the name of every output kind test/e2e has a case of, one per line, for the e2e harness. -/
def main : IO Unit :=
  (Tazuna.Kind.all.filter (·.e2e)).forM fun k => IO.println k.name
