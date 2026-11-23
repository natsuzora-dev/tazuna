const { random } = Math;
const { Now } = Temporal;

export const stamps = () => [
  Date.now(),
  new Date(),
  performance.now(),
  process.argv,
  globalThis.Date,
  Math["random"](),
  random(),
  Now.instant(),
  crypto.randomUUID(),
];

export const loadCrypto = () => import("node:crypto");
