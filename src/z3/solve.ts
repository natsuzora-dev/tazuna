import { init } from "z3-solver";

/**
 * Z3's output on each SMT-LIB script, in order: what the z3 command prints for the script, such as `unsat`, or `sat`
 * followed by a get-value answer. Lean writes the scripts and reads the outputs; this function only runs them.
 */
export async function solve(scripts: readonly string[]): Promise<string[]> {
  if (scripts.length === 0) return [];
  const { Z3, em } = await init();
  try {
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
  } finally {
    em.PThread.terminateAllThreads();
  }
}
