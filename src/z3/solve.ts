import { init } from "z3-solver";

/**
 * The process's one Z3 module. Each init compiles the 39 MB wasm again, reserves another 2 GB of shared memory and
 * spawns fresh worker threads, so the module is made once and kept; its idle workers do not keep the process alive.
 */
let z3: ReturnType<typeof init> | undefined;

/** The parts of the emscripten module that a call with a heap string uses; z3-solver types the module as any. */
type Module = {
  readonly HEAPU8: Uint8Array;
  _malloc(size: number): number;
  _free(pointer: number): void;
  _async_Z3_eval_smtlib2_string(context: unknown, script: number): void;
  async_call(f: (context: unknown, script: number) => void, context: unknown, script: number): Promise<string>;
};

/**
 * Z3's output on each SMT-LIB script, in order: what the z3 command prints for the script, such as `unsat`, or `sat`
 * followed by a get-value answer. Lean writes the scripts and reads the outputs; this function only runs them.
 */
export async function solve(scripts: readonly string[]): Promise<string[]> {
  if (scripts.length === 0) return [];
  z3 ??= init();
  const { Z3, em } = await z3;
  const module = em as Module;
  const outputs: string[] = [];
  for (const script of scripts) {
    const context = Z3.mk_context(Z3.mk_config());
    // z3-solver's eval_smtlib2_string puts the script on the wasm stack, which the call frees on return while Z3's
    // worker thread has yet to read it; under load the thread read a reused stack and Z3 saw a cut script. The script
    // lives on the heap until Z3 answers.
    const bytes = new TextEncoder().encode(script);
    const pointer = module._malloc(bytes.length + 1);
    module.HEAPU8.set(bytes, pointer);
    module.HEAPU8[pointer + bytes.length] = 0;
    try {
      outputs.push(await module.async_call(module._async_Z3_eval_smtlib2_string, context, pointer));
    } finally {
      module._free(pointer);
      Z3.del_context(context);
    }
  }
  return outputs;
}
