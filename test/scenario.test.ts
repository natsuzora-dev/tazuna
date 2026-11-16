import assert from "node:assert/strict";
import { test } from "node:test";
import {
  at,
  elsewhere,
  elsewhereInputs,
  restart,
  scenario,
  subscribe,
  timed,
  unsubscribe,
  writtenPositions,
} from "../src/dsl/scenario.ts";

const peer = {};
const query = { kind: "query", input: {} } as never;

test("The service of a scenario skips its elsewhere inputs, which keep their times, written positions, and the number of the service's inputs before them", () => {
  const s = scenario("", [
    at("2026-10-25T10:00:00+09:00"),
    unsubscribe(subscribe(query, {})),
    at("2026-10-25T11:00:00+09:00"),
    elsewhere(peer, restart()),
    at("2026-10-25T12:00:00+09:00"),
    elsewhere(peer, unsubscribe(subscribe(query, {}))),
  ]);
  assert.deepEqual(
    timed(s).map((i) => [i.type, i.time]),
    [
      ["unsubscribe", "2026-10-25T10:00:00+09:00"],
      ["time", "2026-10-25T11:00:00+09:00"],
      ["time", "2026-10-25T12:00:00+09:00"],
    ],
  );
  assert.deepEqual(writtenPositions(s), [2, 3, 5]);
  assert.deepEqual(
    elsewhereInputs(s).map(({ service, input, position, before }) => [
      service,
      input.type,
      input.time,
      position,
      before,
    ]),
    [
      [peer, "restart", "2026-10-25T11:00:00+09:00", 4, 2],
      [peer, "unsubscribe", "2026-10-25T12:00:00+09:00", 6, 3],
    ],
  );
});
