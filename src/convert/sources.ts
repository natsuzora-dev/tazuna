import { existsSync } from "node:fs";
import { dirname, join } from "node:path";
import {
  type ArrowFunction,
  type FunctionExpression,
  isArrowFunction,
  isFunctionExpression,
  type Node,
} from "typescript/unstable/ast";
import { API, type Checker, type Project } from "typescript/unstable/sync";
import type { Location } from "./located.ts";

/** A spec function's syntax, and the checker that types it. */
export interface Source {
  readonly node: ArrowFunction | FunctionExpression;
  readonly text: string;
  readonly checker: Checker;
}

function nearestTsconfig(folder: string): string | undefined {
  const tsconfig = join(folder, "tsconfig.json");
  if (existsSync(tsconfig)) return tsconfig;
  const parent = dirname(folder);
  return parent === folder ? undefined : nearestTsconfig(parent);
}

const lineStarts = (text: string): number[] => {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") starts.push(i + 1);
  return starts;
};

/** The innermost function of `root` whose text holds `offset`. */
function functionAt(root: Node, offset: number): ArrowFunction | FunctionExpression | undefined {
  let found: ArrowFunction | FunctionExpression | undefined;
  const visit = (node: Node): void => {
    if (offset < node.pos || node.end <= offset) return;
    if (isArrowFunction(node) || isFunctionExpression(node)) found = node;
    node.forEachChild(visit);
  };
  visit(root);
  return found;
}

/** The TypeScript programs of spec files, one per tsconfig.json, each served by a tsgo process. */
export class Sources {
  private readonly apis: API[] = [];
  private readonly projects = new Map<string, Project | undefined>();

  close(): void {
    for (const api of this.apis) api.close();
  }

  private projectOf(tsconfig: string): Project | undefined {
    if (this.projects.has(tsconfig)) return this.projects.get(tsconfig);
    const api = new API({ cwd: dirname(tsconfig) });
    this.apis.push(api);
    const project = api.updateSnapshot({ openProject: tsconfig }).getProject(tsconfig);
    this.projects.set(tsconfig, project);
    return project;
  }

  sourceAt(location: Location): Source | undefined {
    const tsconfig = nearestTsconfig(dirname(location.file));
    const project = tsconfig === undefined ? undefined : this.projectOf(tsconfig);
    const file = project?.program.getSourceFile(location.file);
    if (project === undefined || file === undefined) return undefined;
    const start = lineStarts(file.text)[location.line];
    const node = start === undefined ? undefined : functionAt(file, start + location.column);
    return node === undefined ? undefined : { node, text: file.text, checker: project.checker };
  }
}
