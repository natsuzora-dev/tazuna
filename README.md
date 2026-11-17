# tazuna

tazuna is a language for specifying the behavior of services in TypeScript so that each spec has exactly one meaning.
[docs/guarantees.md](docs/guarantees.md) states what tazuna guarantees, and [docs/writing-specs.md](docs/writing-specs.md) states the rules for writing specs.
Facts about one definition are in its doc comment.

## Get started

tazuna is published to GitHub Packages.
To install it, add the following line to your project's `.npmrc`, and authenticate to GitHub Packages with a token that has the `read:packages` scope:

```
@natsuzora-dev:registry=https://npm.pkg.github.com
```

Then run the following command, and add `"extends": "@natsuzora-dev/tazuna/tsconfig.base.json"` to your `tsconfig.json`:

```sh
npm install -D @natsuzora-dev/tazuna typescript zod @types/node
```

For a complete project, see the ToDo sample in [samples/todo](samples/todo).

To list the commands and their options, run `npx tazuna --help`.

## Spec folder layout

Each folder directly under the spec folder holds one service, and the folder name is the service name, which its `service()` or `externalService()` call writes as `name` so that types can carry it.
For example, `spec/todo/` holds the `todo` service.

A service folder holds one file for each kind of definition:

| File | Definitions |
|---|---|
| `data.ts` | Entities, the `service()` or `externalService()` call, and the `constants()` call |
| `events.ts` | Events |
| `commands.ts` | Commands |
| `queries.ts` | Queries |
| `automations.ts` | Automations |
| `machines.ts` | Machines |
| `<name>Screen.ts` | One screen. Screens belong to the `screens` service, which has no entities. |
| `contract.ts` | The contract |
| `scenarios.ts` | Scenarios |

Each folder has at most one `constants()` call, exported as `<folder name>Constants`.
For example, `spec/todo/` has `todoConstants`.

These file names are a convention, and tazuna doesn't check them.
The `check`, `test`, and `verify` commands collect the exported definitions, contracts, constants, and scenarios from every `.ts` file in the spec folder, except the files under `__snapshots__`.
