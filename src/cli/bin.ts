import { main } from "./main.ts";

process.exitCode = await main(process.argv.slice(2), {
  cwd: process.cwd(),
  log: (line) => console.log(line),
  error: (line) => console.error(line),
});
