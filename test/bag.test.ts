import assert from "node:assert/strict";
import { test } from "node:test";
import { z } from "zod";
import { type Bag, BagValue, NotOnly } from "../src/data/bag.ts";
import { bag, bagged, sortCollections } from "../src/data/collections.ts";
import { jsonSchema } from "../src/data/jsonSchema.ts";
import type { DateLabel } from "../src/data/time.ts";

const bagOf = <T>(items: readonly T[]): Bag<T> => new BagValue(() => items);
const numbers = (bag: Bag<number>) => bag.sortedBy((n) => n).map((run) => [run.min((n) => n), run.size]);

test("A Bag filters, maps, flattens and concatenates without exposing an order", () => {
  const bag = bagOf([3, 1, 2]);
  assert.deepEqual(numbers(bag.filter((n) => n > 1)), [
    [2, 1],
    [3, 1],
  ]);
  assert.deepEqual(numbers(bag.flatMap((n) => (n > 2 ? bagOf([n, n]) : [n * 10]))), [
    [3, 2],
    [10, 1],
    [20, 1],
  ]);
  assert.deepEqual(numbers(bag.map((n) => n % 2).concat(bagOf([5]))), [
    [0, 1],
    [1, 2],
    [5, 1],
  ]);
  assert.equal(bag.size, 3);
});

test("some and every call the predicate on every value", () => {
  const seen: number[] = [];
  assert.equal(
    bagOf([1, 2, 3]).some((n) => seen.push(n) > 0),
    true,
  );
  assert.equal(
    bagOf([1, 2, 3]).every((n) => seen.push(n) < 0),
    false,
  );
  assert.deepEqual(seen, [1, 2, 3, 1, 2, 3]);
});

test("min and max return the key and throw on NaN, sum takes only safe integers", () => {
  const days = bagOf(["2026-03-01", "2026-01-31"] as DateLabel[]);
  assert.equal(
    days.min((d) => d),
    "2026-01-31",
  );
  assert.equal(
    days.max((d) => Number(d.slice(8))),
    31,
  );
  assert.equal(
    bagOf<number>([]).min((n) => n),
    undefined,
  );
  assert.equal(
    bagOf([1, 2]).sum((n) => n),
    3,
  );
  assert.throws(() => bagOf([1, Number.NaN]).min((n) => n), RangeError);
  assert.throws(() => bagOf([Number.NaN, 1]).sortedBy((n) => n), RangeError);
  assert.throws(() => bagOf([0.5]).sum((n) => n), RangeError);
  assert.throws(() => bagOf([Number.MAX_SAFE_INTEGER, 1]).sum((n) => n), RangeError);
  assert.equal(
    bagOf([Number.MAX_SAFE_INTEGER, 1, -2]).sum((n) => n),
    Number.MAX_SAFE_INTEGER - 1,
  );
});

test("only returns the one value, undefined for none, and throws NotOnly for more", () => {
  assert.equal(bagOf(["a"]).only(), "a");
  assert.equal(bagOf([]).only(), undefined);
  assert.throws(() => bagOf(["a", "b"]).only(), NotOnly);
});

test("sortedBy groups equal keys into one run", () => {
  const runs = bagOf([
    { id: "b", day: 2 },
    { id: "a", day: 1 },
    { id: "c", day: 2 },
  ]).sortedBy((r) => r.day);
  assert.deepEqual(
    runs.map((run) => run.size),
    [1, 2],
  );
  assert.equal(runs[0]?.only()?.id, "a");
});

test("A Bag reads its values on each call", () => {
  let reads = 0;
  const bag = new BagValue(() => {
    reads++;
    return [1];
  });
  assert.equal(reads, 0);
  void bag.size;
  void bag.only();
  assert.equal(reads, 2);
});

test("sortCollections and bagged order a bag in an object's catchall like one in its shape", () => {
  const schema = z.object({ named: bag(z.int()) }).catchall(bag(z.int()));
  assert.deepEqual(sortCollections(jsonSchema(schema), { named: [2, 1], other: [3, 1, 2] }), {
    named: [1, 2],
    other: [1, 2, 3],
  });
  const received = bagged(schema, { other: [1, 2] }) as { readonly other: unknown };
  assert.ok(received.other instanceof BagValue);
});
