// A const at the top of a module, a let inside a function, and a destructured Temporal member hold no module state.
const { Instant } = Temporal;

export const start = Instant.from("2026-10-25T00:00:00Z");

export const count = (titles: readonly string[]) => {
  let n = 0;
  for (const _ of titles) n += 1;
  return n;
};
