// Feeds the `in` lines of each spec trace under a directory (search's inputs or the scenarios' snapshots) to the
// service the trace names, and writes the service's own trace of the run under another directory, for `verify`.
// Usage: node tazuna/replay.ts <traces to replay> <directory to write>

import { mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { postWebhook } from "../src/server/fakes/webhook.ts";
import { ManualClock } from "../src/server/platform/clock.ts";
import { gatewayWebhook } from "./mapping.ts";
import { recordedShop, webhookSecret } from "./recorded-shop.ts";
import type { Line } from "./recorder.ts";

// biome-ignore lint/suspicious/noExplicitAny: trace lines are untyped JSON
type Json = any;

const roles: Record<string, "customer" | "staff"> = { Customer: "customer", Staff: "staff" };

async function replay(lines: Json[], service: string): Promise<Line[]> {
  const clock = new ManualClock(0);
  const { shop, services, recorders } = recordedShop({ names: [service], clock });
  const recorder = recorders.get(service);
  const [target] = services;
  if (!recorder || !target) throw new Error(`unknown service ${service}`);
  const { mapping } = recorder;

  // The ids a run made, in order. A spec trace names them id1, r1, ...; the service names the same things in the same
  // order its own way, so the n-th name of one is the n-th of the other. An id neither made comes from outside.
  const made = (trace: Json[]) =>
    trace.flatMap((line) =>
      line.out === "request" ? [line.id] : line.out === "event" ? mapping.makes(line.value) : [],
    );
  const ours = (spec: Json[], value: Json): Json => {
    const specNames = made(spec);
    const own = made(recorder.lines);
    const rename = (v: Json): Json =>
      typeof v === "string"
        ? (own[specNames.indexOf(v)] ?? v)
        : Array.isArray(v)
          ? v.map(rename)
          : v && typeof v === "object"
            ? Object.fromEntries(Object.entries(v).map(([k, x]) => [k, rename(x)]))
            : v;
    return rename(value);
  };

  const cookies = new Map<string, string>();
  const signIn = async (role: string) => {
    if (!cookies.has(role)) {
      const response = await shop.app.request("/api/session", {
        method: "PUT",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ role }),
      });
      cookies.set(role, (response.headers.get("set-cookie") ?? "").split(";")[0] ?? "");
    }
    return cookies.get(role) ?? "";
  };

  for (const [index, line] of lines.entries()) {
    if (!line.in) continue;
    clock.set(line.time);
    const before = lines.slice(0, index);
    switch (line.in) {
      case "request": {
        const op = mapping.requests.find((request) => request.name === line.name);
        if (!op) throw new Error(`${service} has no request ${line.name}`);
        const input = ours(before, line.input);
        if (!op.route || !op.request) {
          // The app has no route for a command that only the service runs, so no outside caller can reach it.
          await recorder.input(async () => {
            recorder.write({ in: "request", id: line.id, name: line.name, caller: line.caller, input });
            recorder.write({ out: "answer", to: line.id, outcome: "invalid", rules: ["callers"] });
          });
          break;
        }
        const { params = {}, query, body } = op.request(input);
        const path = op.route.path.replace(/:(\w+)/g, (_, name) => encodeURIComponent(params[name] ?? ""));
        const search = query ? `?${new URLSearchParams(query)}` : "";
        const headers: Record<string, string> = { cookie: await signIn(roles[line.caller.tag] ?? "") };
        if (body !== undefined) headers["content-type"] = "application/json";
        await shop.app.request(`/api/${service}${path}${search}`, {
          method: op.route.method,
          headers,
          body: body === undefined ? undefined : JSON.stringify(body),
        });
        break;
      }
      case "event": {
        const inbound = mapping.inbound.find((entry) => entry.source === line.name && entry.tag === line.value.tag);
        if (!inbound) throw new Error(`${service} has no inbound event ${line.name} ${line.value.tag}`);
        await target.handle({ id: index, type: inbound.type, payload: inbound.fromSpec(ours(before, line.value)) });
        break;
      }
      case "answer": {
        const to = ours(before, line.to);
        const request = before.find((out) => out.out === "request" && out.id === line.to);
        if (request?.external === "payment gateway") {
          await postWebhook(shop.app, gatewayWebhook(request.name, line, to), webhookSecret);
        } else {
          // The shop does not read the mail provider's delivery reports.
          const { in: _, time: __, ...answer } = line;
          await recorder.input(async () => recorder.write({ in: "answer", ...answer, to }));
        }
        break;
      }
      case "clock":
        await shop.tick();
        break;
    }
  }
  return recorder.lines;
}

function* traces(dir: string): Generator<string> {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name);
    if (entry.isDirectory()) yield* traces(path);
    else if (entry.name.endsWith(".jsonl")) yield path;
  }
}

const [from, to] = process.argv.slice(2);
if (!from || !to) throw new Error("usage: node tazuna/replay.ts <traces to replay> <directory to write>");
rmSync(to, { recursive: true, force: true });
for (const file of traces(from)) {
  const [header, ...lines] = readFileSync(file, "utf8")
    .trim()
    .split("\n")
    .map((text) => JSON.parse(text));
  const out = join(to, relative(from, file));
  mkdirSync(dirname(out), { recursive: true });
  const trace = await replay(lines, header.service);
  writeFileSync(out, `${trace.map((line) => JSON.stringify(line)).join("\n")}\n`);
}
