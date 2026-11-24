import Tazuna.Cli.Kind

/-- Prints the name of every output kind, one per line, for the e2e harness. -/
def main : IO Unit :=
  Tazuna.Kind.all.forM fun k => IO.println k.name
