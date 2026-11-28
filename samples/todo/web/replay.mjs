// Feeds the in lines of each trace in a directory (search's inputs or a scenario's snapshot) to the implementation
// and writes the implementation's own trace of the run to another directory, for `verify`.
// Usage: node replay.mjs <traces to replay> <directory to write>

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { createTodo } from "./todo.mjs";

const [from, to] = process.argv.slice(2);
mkdirSync(to, { recursive: true });

// The names a run made, in order: task ids and mail request ids.
const made = (lines) =>
  lines.flatMap((line) =>
    line.out === "event" && line.value.tag === "Added" ? [line.value.task] : line.out === "request" ? [line.id] : [],
  );

for (const file of readdirSync(from).filter((name) => name.endsWith(".jsonl"))) {
  const [header, ...lines] = readFileSync(join(from, file), "utf8").trim().split("\n").map((line) => JSON.parse(line));
  const trace = [header];
  const todo = createTodo((line) => trace.push(line));

  lines.forEach((line, index) => {
    // An in line names what the spec made by the spec's names (id1, r1). The implementation made the same things in
    // the same order under its own names (task-1, mail-1), so the n-th name of one is the n-th of the other.
    const spec = made(lines.slice(0, index));
    const own = made(trace);
    const ours = (name) => own[spec.indexOf(name)] ?? name;
    switch (line.in) {
      case "request": {
        const request = line.name === "complete" || line.name === "remind" ? { ...line, input: ours(line.input) } : line;
        trace.push(request);
        todo.request(request);
        break;
      }
      case "answer": {
        const answer = { ...line, to: ours(line.to) };
        trace.push(answer);
        todo.answer(answer);
        break;
      }
      case "clock":
        trace.push(line);
        todo.clock(line.time);
        break;
    }
  });

  writeFileSync(join(to, file), trace.map((line) => JSON.stringify(line)).join("\n") + "\n");
}
