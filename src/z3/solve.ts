import { init } from "z3-solver";

/**
 * The process's one Z3 module. Each init compiles the 39 MB wasm again, reserves another 2 GB of shared memory and
 * spawns fresh worker threads, so the module is made once and kept; its idle workers do not keep the process alive.
 */
let z3: ReturnType<typeof init> | undefined;

/**
 * Z3's output on each SMT-LIB script, in order: what the z3 command prints for the script, such as `unsat`, or `sat`
 * followed by a get-value answer. Lean writes the scripts and reads the outputs; this function only runs them.
 */
export async function solve(scripts: readonly string[]): Promise<string[]> {
  if (scripts.length === 0) return [];
  z3 ??= init();
  const { Z3 } = await z3;
  const outputs: string[] = [];
  for (const script of scripts) {
    const context = Z3.mk_context(Z3.mk_config());
    try {
      outputs.push(await Z3.eval_smtlib2_string(context, script));
    } finally {
      Z3.del_context(context);
    }
  }
  return outputs;
}
