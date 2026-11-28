# The shop's web implementation

This is the shop from [`../spec`](../spec) as a team would build it today: a React app in the browser, and one Node server that runs the three services and serves the app.
`tazuna verify` compares what the services do with the spec; see [Check it against the spec](#check-it-against-the-spec).

## How the services work together

- Each service is a module under `src/server/` with its own SQLite database, its own routes under `/api/<service>`, and its own outbox. No service reads another's tables or calls another's code.
- A service writes the events it publishes to its outbox in the same transaction as the change they report. The relay in `src/server/platform/relay.ts` delivers them to the services that subscribe, at least once. A consumer parses only the fields it reads, so a publisher can add fields freely.
- Orders cancels unpaid orders in a scheduled job, `expireUnpaidOrders`, which `src/server/main.ts` runs every 5 seconds. Every service reads time from an injected `Clock`, so tests move time with `ManualClock` instead of waiting.
- Payments sends charges and refunds to the payment gateway and learns each outcome from the gateway's signed webhook, the way card gateways report asynchronous results.
- The gateway and the mail provider are outside systems that the sample has no account with. `src/server/fakes/` holds a simulated gateway, which approves every charge in `npm start`, and a mailer that logs.
- Sign-in is a stub: anyone can sign in as a customer or as staff. A real deployment replaces `src/server/platform/session.ts` with its identity provider and keeps the `requireRole` checks.

## The stack, and why

Each version is pinned exactly and was released by 2026-11-15, at least two weeks before this sample.
The choices were compared in November 2026 by npm downloads and by what the spec needs.

| Concern | Choice | Compared with | Why |
| --- | --- | --- | --- |
| API | Hono 4.13, typed RPC through `hono/client` | TanStack Start 1.169 server functions, Next.js 16 route handlers, Express, oRPC, tRPC | `app.request()` runs a request in-process through the real routes, validation, and sign-in, which the unit tests and the trace replay both need. Start and Next.js run their handlers only inside their own runtime. The RPC client comes from the route types, with no extra layer. |
| UI | React 19 single-page app, TanStack Router and Query, Vite 8 | TanStack Start, Next.js | The shop needs no server rendering, and the API is the boundary the services own. |
| Validation | Zod 4 | Valibot | Parses every boundary: request bodies, consumed events, and webhooks. |
| Data | Drizzle ORM 0.45, better-sqlite3 13, drizzle-kit migrations | Prisma | SQL-shaped schema in TypeScript, synchronous transactions on SQLite, and one migration folder per service. |
| Tests | Vitest 5, Playwright 1.65 | Jest, Cypress | Vitest shares the Vite config; Playwright is the most used end-to-end runner. |
| Lint and format | Biome 2.6 | ESLint with Prettier | One tool and one config. ESLint with Prettier is used more, but needs four packages and two configs here. |
| Runtime | Node 24 or later, running TypeScript directly | tsx | Node strips types itself. TypeScript 7 only type-checks. |

## Run the shop

```sh
npm ci
npm run build
npm start
```

The shop listens on http://localhost:3000 and keeps its databases in `data/`.
For development, run `npm run dev:api` and `npm run dev` side by side; Vite serves the app on port 5173 and passes `/api` to the server.

`npm test` runs the services' tests.
`npm run e2e` builds the app, starts `e2e/server.ts`, and runs the Playwright tests in `e2e/`; run `npx playwright install chromium` once first.

## Check it against the spec

`tazuna/` is the only code that knows the spec, and the app never imports it:

- `mapping.ts` reads each service's boundary in the spec's terms: which route is which command or query, which published event is which spec event, and which webhook answers which request.
- `recorder.ts` records one trace per service. Each input to the service is an `in` line, and its answer, the events it publishes, and the requests it sends out are that input's `out` lines.
- `recorded-shop.ts` builds the services on in-memory databases with a recorder each.
- `replay.ts` feeds the spec's traces to one service at a time and writes the service's own trace. `e2e/server.ts` records every Playwright test, one trace per service.

`verify` needs Gleam and an engine, as [the shop's README](../README.md#before-you-start) says.
`npm run verify` replays `../spec/inputs` and `../spec/snapshots` into `traces/` and verifies them.
After `npm run e2e`, `npm run verify:e2e` verifies the traces in `e2e-traces/`.

The recorder relies on these facts about the app:

- The spec's out events come from the outbox. An outbox event that `mapping.ts` does not name stops the recording.
- A trace puts all of an input's out lines before the next `in` line. The app takes inputs concurrently, so the recorder lets one input at a time into each service.
- A trace starts at time 0 when its recorder starts. No outcome in the spec depends on where time starts.
- Reads the spec does not model, such as the price list at `GET /api/orders/prices` and sign-in, are not recorded.

Two kinds of spec input have no counterpart in the app, and the replay writes their lines itself.
A command only the service runs, such as `hold` or `confirm`, has no route, so an outside request for it is refused with `invalid callers`.
An answer from the mailer reaches nothing, because the shop does not read delivery reports.
