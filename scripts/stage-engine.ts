import { execFileSync } from "node:child_process";
import { copyFileSync, existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

const manifest = JSON.parse(readFileSync("package.json", "utf8")) as {
  readonly name: string;
  readonly os: readonly string[];
  readonly cpu: readonly string[];
  readonly files: readonly string[];
};
const [binary] = manifest.files;
const built = join(import.meta.dirname, "../lean/.lake/build/bin", binary ?? "");

if (!manifest.os.includes(process.platform) || !manifest.cpu.includes(process.arch))
  throw new Error(
    `${manifest.name} packs a binary built on its own platform, not on ${process.platform}-${process.arch}.`,
  );
if (binary === undefined || !existsSync(built)) throw new Error(`No ${built}. Run lake build tazuna-engine in lean.`);
copyFileSync(built, binary);
if (process.platform !== "win32") execFileSync("strip", [binary]);
