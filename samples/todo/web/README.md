# ToDo sample implementation

This web app implements the ToDo app that `../spec` specifies, with TanStack Start, oRPC, TanStack Query, Drizzle, and React.

## Run the app

```sh
npm run dev      # https://localhost:3000 (self-signed certificate)
npm run build
npm run start    # the built server
```

The database is the SQLite file that `DB_FILE_NAME` in `.env` names.
After you change `src/db/schema.ts`, run `npm run db:generate` to create a migration.

## Test the app

```sh
npm test
npm run test:e2e
npm run check
```

## How the app uses tazuna

The app reads only schemas and constants from `@todo/spec`.
The tests check the spec with `checkSpec` and drive the app through the snapshots of its scenarios with `drive`, both from `@natsuzora-dev/tazuna/verify`, and `tazuna verify` compares the traces that the app records with the snapshots.
