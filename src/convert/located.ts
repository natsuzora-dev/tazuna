import { Session } from "node:inspector";
import { fileURLToPath } from "node:url";

/** Where a function's source starts: a file, and a zero-based line and column. */
export interface Location {
  readonly file: string;
  readonly line: number;
  readonly column: number;
}

/**
 * Finds where functions start through the inspector protocol, which V8 answers synchronously in this thread. A spec
 * file runs with its types stripped to spaces, so a position in the run is the same position in the .ts source.
 */
export class Locator {
  private readonly session = new Session();
  private readonly files = new Map<string, string>();

  constructor() {
    this.session.connect();
    this.session.on("Debugger.scriptParsed", ({ params }) => {
      if (params.url.startsWith("file:")) this.files.set(params.scriptId, fileURLToPath(params.url));
    });
    this.session.post("Debugger.enable");
  }

  close(): void {
    this.session.disconnect();
  }

  located(f: (...args: never[]) => unknown): Location | undefined {
    const global = globalThis as { __tazunaLocated?: unknown };
    global.__tazunaLocated = f;
    let found: Location | undefined;
    this.session.post("Runtime.evaluate", { expression: "globalThis.__tazunaLocated" }, (_, evaluated) => {
      const objectId = evaluated?.result.objectId;
      if (objectId === undefined) return;
      this.session.post("Runtime.getProperties", { objectId, ownProperties: true }, (__, properties) => {
        const at = properties?.internalProperties?.find((p) => p.name === "[[FunctionLocation]]")?.value?.value as
          | { readonly scriptId: string; readonly lineNumber: number; readonly columnNumber: number }
          | undefined;
        const file = at === undefined ? undefined : this.files.get(at.scriptId);
        if (at !== undefined && file !== undefined) found = { file, line: at.lineNumber, column: at.columnNumber };
      });
      this.session.post("Runtime.releaseObject", { objectId });
    });
    delete global.__tazunaLocated;
    return found;
  }
}
