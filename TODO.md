# TODO

- Decide whether to model several services in one Lean run, so that the messages a scenario takes from another service could be checked against that service's run rather than only its contract (the Other services assumption).
- When dependency-cruiser supports TypeScript 7's tsc for parsing (18.7.2 supports `>=2.0.0 <7.0.0`), remove `parser: "swc"` from `.dependency-cruiser.json`, the `@swc/core` devDependency, its knip `ignoreDependencies` entry, and its `allowScripts` entry in `package.json`.
