/**
 * Lean's Limit.max, by limit name. Exceeding a limit halts with the Fault named `exceeded` and the limit's name, such
 * as exceededCommandDepth.
 */
export const limits = {
  /** The depth of a chain of own-service commands. */
  commandDepth: 100,
  /** The own-service commands in one message. */
  messageCommands: 10_000,
  /** The always rounds in one settle. */
  alwaysRounds: 100,
  /** The onDone selections in one onDone work. */
  onDoneSelections: 10_000,
  /** The work items and commands in one message. */
  messageWork: 100_000,
  /** The deadlines in one clock advance. */
  dueDeadlines: 10_000,
  /** The nesting depth of exits (copies, and screens that their parent's exit closes). */
  exitDepth: 100,
} as const;
