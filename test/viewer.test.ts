import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";

const src = join(import.meta.dirname, "../viewer/src");
const read = (file: string) => readFileSync(join(src, file), "utf8").replaceAll(/\/\*[\s\S]*?\*\//g, "");
const css = read("style.css");
const tsx = readdirSync(src)
  .filter((f) => f.endsWith(".tsx"))
  .map((f) => readFileSync(join(src, f), "utf8"));

test("style.css of the viewer writes colors, lengths, font sizes, and durations as tokens.css variables, not literal values", () => {
  const literals = [
    ...css.matchAll(/#[0-9a-f]{3,8}\b/gi),
    ...css.matchAll(/\b(?:rgba?|hsla?|hwb|lab|lch|oklab|oklch|color)\(/gi),
    ...css.matchAll(/(?<![\w-])\d*\.?\d+(?:px|r?em|[sdl]?v[hw]|vmin|vmax|ch|ex|pt|pc|cm|mm|in|q|m?s)\b/gi),
    ...[
      ...css.matchAll(
        /(?:^|[;{\s])(?:color|background(?:-color)?|fill|stroke|(?:border|outline)(?:-\w+)?-color):([^;}]*)/g,
      ),
    ]
      .map((m) => (m[1] ?? "").replaceAll(/var\([^)]*\)/g, ""))
      .flatMap((value) => value.match(/[a-z]+/gi) ?? [])
      .filter((word) => !["inherit", "currentColor", "transparent", "none"].includes(word)),
  ].map((m) => (typeof m === "string" ? m : m[0]));
  assert.deepEqual(literals, []);
});

test("tokens.css defines every variable that style.css and the TSX files of the viewer read", () => {
  const defined = new Set([...read("tokens.css").matchAll(/(--[\w-]+)\s*:/g)].map((m) => m[1]));
  const used = [...[css, ...tsx].join("\n").matchAll(/(?:var\(|cssPx\(")(--[\w-]+)/g)].map((m) => m[1]);
  assert.notEqual(used.length, 0);
  assert.deepEqual(
    used.filter((name) => !defined.has(name)),
    [],
  );
});

test("style.css, the TSX files, or other variables read every variable that tokens.css defines", () => {
  const tokens = read("tokens.css");
  const defined = [...tokens.matchAll(/(--[\w-]+)\s*:/g)].map((m) => m[1] ?? "");
  const used = [...[css, ...tsx, tokens].join("\n").matchAll(/(?:var\(|cssPx\(")(--[\w-]+)/g)].map((m) => m[1]);
  assert.deepEqual(
    defined.filter((name) => !used.includes(name)),
    [],
  );
});
