import { emit, service } from "@natsuzora-dev/tazuna";

export const { command, machine, event, contract, scenario } = service({ name: "todo", description: "Keep chores" });

export const milkBought = event({});
export const roomDusted = event({});
export const celebrated = event({});

export const buyMilk = command({ callers: ["client"], emits: [milkBought] }).decide(() => [emit(milkBought, {})]);

export const dustRoom = command({ callers: ["client"], emits: [roomDusted] }).decide(() => [emit(roomDusted, {})]);

export const celebrate = command({ callers: ["client", "todo"], emits: [celebrated] }).decide(() => [
  emit(celebrated, {}),
]);
