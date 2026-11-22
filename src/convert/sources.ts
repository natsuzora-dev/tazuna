import { dirname } from "node:path";
import {
  type ArrowFunction,
  type FunctionExpression,
  isArrowFunction,
  isFunctionExpression,
  isMethodDeclaration,
  type MethodDeclaration,
  type Node,
} from "typescript/unstable/ast";
import { API, type Checker, type Project } from "typescript/unstable/sync";
import type { Location } from "./located.ts";

/** A spec function as it can be written: an arrow, a function expression, or a method of an object literal. */
export type SpecFunctionNode = ArrowFunction | FunctionExpression | MethodDeclaration;

/** A spec function's syntax, the file it is in, and the checker that types it. */
export interface Source {
  readonly node: SpecFunctionNode;
  readonly file: Node;
  readonly text: string;
  readonly checker: Checker;
}

const lineStarts = (text: string): number[] => {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") starts.push(i + 1);
  return starts;
};

/** The innermost function of `root` whose text holds `offset`. */
function functionAt(root: Node, offset: number): SpecFunctionNode | undefined {
  let found: SpecFunctionNode | undefined;
  const visit = (node: Node): void => {
    if (offset < node.pos || node.end <= offset) return;
    if (isArrowFunction(node) || isFunctionExpression(node) || isMethodDeclaration(node)) found = node;
    node.forEachChild(visit);
  };
  visit(root);
  return found;
}

/**
 * The TypeScript programs of spec files, served by one tsgo process: each file's configured project, the one whose
 * tsconfig.json holds it, or else an inferred project, as an editor opens a file.
 */
export class Sources {
  private api: API | undefined;
  private readonly projects = new Map<string, Project | undefined>();

  close(): void {
    this.api?.close();
  }

  private projectOf(file: string): Project | undefined {
    if (this.projects.has(file)) return this.projects.get(file);
    this.api ??= new API({ cwd: dirname(file) });
    const project = this.api.updateSnapshot({ openFiles: [file] }).getDefaultProjectForFile(file);
    this.projects.set(file, project);
    return project;
  }

  sourceAt(location: Location): Source | undefined {
    const project = this.projectOf(location.file);
    const file = project?.program.getSourceFile(location.file);
    if (project === undefined || file === undefined) return undefined;
    const start = lineStarts(file.text)[location.line];
    const node = start === undefined ? undefined : functionAt(file, start + location.column);
    return node === undefined ? undefined : { node, file, text: file.text, checker: project.checker };
  }
}
