# TODO

- Decide whether to extend the reversed-key-order audit (`OrderDependent.reversedRecords`) from queries to the other spec functions. A measured extension made a spec's `test` 28% slower and changed results in 327 calls; extending it needs, per function kind, a rule for which results count as equal.
- Guarantees: for each property that `docs/PRINCIPLES.md` claims (each axis and the group that reports it), find what backs it: a Lean theorem, the TS–Lean differential tests, or nothing. Then prove in Lean only the missing ones whose failure would mislead users (e.g. if `test` reports no ChoiceDependent violation, the result does not depend on the choices). No separate guarantee document.
- When dependency-cruiser supports TypeScript 7's tsc for parsing (18.7.2 supports `>=2.0.0 <7.0.0`), remove `parser: "swc"` from `.dependency-cruiser.json`, the `@swc/core` devDependency, its knip `ignoreDependencies` entry, and its `allowScripts` entry in `package.json`.
