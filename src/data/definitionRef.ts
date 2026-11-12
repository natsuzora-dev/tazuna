/** A type rather than an interface, so that it fits `Json` in violation data. */
export type DefinitionRef = {
  readonly service: string;
  readonly name: string;
};

export function sameRef(a: DefinitionRef | null, b: DefinitionRef | null): boolean {
  return a !== null && b !== null && a.service === b.service && a.name === b.name;
}
