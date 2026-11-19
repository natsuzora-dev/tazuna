export const sorted = (titles: readonly string[]) => titles.toSorted((a, b) => a.localeCompare(b));
