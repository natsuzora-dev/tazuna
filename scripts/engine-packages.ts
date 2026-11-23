import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { enginePlatforms } from "../src/cli/engine.ts";

const root = join(import.meta.dirname, "..");
const manifestPath = join(root, "package.json");
const manifest = JSON.parse(readFileSync(manifestPath, "utf8")) as Record<string, unknown> & { version: string };
const json = (value: unknown) => `${JSON.stringify(value, null, 2)}\n`;

const names = enginePlatforms.map((platform) => {
  const [os, cpu] = platform.split("-");
  const name = `@natsuzora-dev/tazuna-engine-${platform}`;
  const binary = os === "win32" ? "tazuna-engine.exe" : "tazuna-engine";
  mkdirSync(join(root, "npm", platform), { recursive: true });
  writeFileSync(
    join(root, "npm", platform, "package.json"),
    json({
      name,
      version: manifest.version,
      description: `The engine of @natsuzora-dev/tazuna for ${platform}.`,
      repository: manifest["repository"],
      license: manifest["license"],
      os: [os],
      cpu: [cpu],
      files: [binary],
      scripts: { prepack: "node ../../scripts/stage-engine.ts" },
      publishConfig: manifest["publishConfig"],
    }),
  );
  return name;
});

manifest["optionalDependencies"] = Object.fromEntries(names.map((name) => [name, manifest.version]));
writeFileSync(manifestPath, json(manifest));
