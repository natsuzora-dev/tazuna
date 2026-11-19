import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { test } from "node:test";
import { exampleFolders, explanations } from "../scripts/explain.ts";
import { explain, explanationsPath } from "../src/cli/explain.ts";
import { type Kind, kinds } from "../src/data/kinds.ts";
import { expectedOf, kindOfLine } from "./expected.ts";

const maxExcerptLines = 40;
const built = explanations();
const kindEntries = kinds.map((kind) => [kind, built.kinds[kind]] as const);

test("explain.json is what scripts/explain.ts builds", () => {
  assert.deepEqual(JSON.parse(readFileSync(explanationsPath, "utf8")), built);
});

test("Each group and each kind has a doc comment", () => {
  assert.deepEqual(
    Object.entries(built.groups).filter(([, doc]) => doc === ""),
    [],
  );
  assert.deepEqual(
    kindEntries.filter(([, k]) => k.meaning === ""),
    [],
  );
});

/** The kinds without an example, each with why, until the owner decides whether each stays a user-facing kind. */
const withoutExample: Readonly<Partial<Record<Kind, string>>> = {
  "InvalidScenario.repeatedPeer": "Given's peers type rejects a service listed twice",
  "InvalidScenario.missingRecord": "Given's records type requires the record of each single entity",
  "InvalidScenario.malformedValue": "AnswerOf types each answer, Instant types each time, and check parses each time",
  "InvalidScenario.unrefusable": "net.refuse takes only a request",
  "InvalidScenario.notALook": "offered and notOffered take only a look line",
  "InvalidScenario.misplacedCreated": "created() types only in a running peer's message, and raw() hides it",
  "InvalidScenario.writtenGivenKey": "check reports a created key in Given as Malformed.writtenCreatedKey first",
  "InvalidInput.unownedTarget": "the request types take only definitions of the service that the request reaches",
  "InvalidInput.unlistedRejectionReason": "an answer's type takes as reason only a requires condition of the request",
  "InvalidInput.unknownControl": "operate takes only a control of the screen",
  "InvalidInput.unreadyStep": "only test's own step-order search writes a step order",
  "InvalidInput.unusedStepOrder": "only test's own step-order search writes a step order",
  "Fault.exceededMessageWork":
    "a spec can reach the limit, but 100001 work items in one message run test out of memory",
  "Fault.exceededExitDepth": "a spec can reach the limit, but only through about 50 nested screen definitions",
  "ChoiceDependent.uncomparable":
    "a spec can reach it, but only through equal requests with different answers and seven created records that only their keys tell apart",
  "Mismatch.after": "only test's step-order search reports it, inside the difference of a ChoiceDependent.stepOrder",
};

test("Each kind has one example, the folder under test named after it, which reports that kind and no other, except the kinds without one", () => {
  const folders = exampleFolders();
  assert.deepEqual(
    kinds.filter((kind) => folders.filter(([k]) => k === kind).length !== (withoutExample[kind] === undefined ? 1 : 0)),
    [],
  );
  assert.deepEqual(
    folders
      .filter(([kind, dir]) => {
        const reported = expectedOf(dir).map(kindOfLine);
        return reported.length === 0 || reported.some((k) => k !== kind);
      })
      .map(([, dir]) => relative(join(import.meta.dirname, ".."), dir)),
    [],
  );
});

test(`Each example's excerpt has at most ${maxExcerptLines} lines and holds the reported line`, () => {
  assert.deepEqual(
    kindEntries
      .flatMap(([kind, k]) => (k.example?.excerpt === undefined ? [] : [{ kind, ...k.example.excerpt }]))
      .filter(({ from, to, line }) => to - from >= maxExcerptLines || line < from || line > to)
      .map(({ kind }) => kind),
    [],
  );
});

test("explain marks the reported line of the excerpt, and names an unknown kind and a missing explain.json as misuses", () => {
  const explained = explain("Fault.failedEnsures");
  assert.ok("markdown" in explained);
  const excerpt = built.kinds["Fault.failedEnsures"].example?.excerpt;
  assert.ok(excerpt !== undefined);
  assert.match(explained.markdown, new RegExp(`^> +${excerpt.line} \\| `, "m"));
  assert.deepEqual(explain("Fault.data"), { misuse: "unknown kind Fault.data" });
  assert.deepEqual(explain("constructor"), { misuse: "unknown kind constructor" });
  assert.deepEqual(explain("Fault.failedEnsures", "/missing/explain.json"), {
    misuse: "/missing/explain.json is missing. Reinstall tazuna",
  });
});
