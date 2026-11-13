# TODO

- Decide whether to extend the reversed-key-order audit (`OrderDependent.reversedRecords`) from queries to the other spec functions. A measured extension made a spec's `test` 28% slower and changed results in 327 calls; extending it needs, per function kind, a rule for which results count as equal.
- Decide whether `verify` should report the trace pairs that the `Narrowed` hypothesis of `compare_complete` excludes (repeated IDs, an answer to the implementation's own request, bags in an opened subscription's input). Each now passes `verify` while differing from its snapshot; reporting them removes the matching conditions from `docs/guarantees.md`.
- Decide whether to model several services in one Lean run, so that the messages a scenario takes from another service could be checked against that service's run rather than only its contract (the Other services assumption).
- When dependency-cruiser supports TypeScript 7's tsc for parsing (18.7.2 supports `>=2.0.0 <7.0.0`), remove `parser: "swc"` from `.dependency-cruiser.json`, the `@swc/core` devDependency, its knip `ignoreDependencies` entry, and its `allowScripts` entry in `package.json`.
