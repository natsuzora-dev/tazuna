import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { sensor } from "../sensor/contract.ts";

export const Door = singleEntity({
  description: "Whether the door was opened, and whether someone knocked",
  fields: { opened: z.boolean().default(false), knocked: z.boolean().default(false) },
});

export const { command, automation, machine, updateEvent } = service({
  name: "panel",
  description: "Note the door's reports, and ring once on starting when the door was opened",
  entities: { Door },
});

export const openNoted = updateEvent({ entity: Door, writes: ["opened"] });
export const knockNoted = updateEvent({ entity: Door, writes: ["knocked"] });

export const noteOpen = command({ callers: ["panel"], emits: [openNoted] }).decide(() => [
  emit(openNoted, { opened: true }),
]);

export const noteKnock = command({ callers: ["panel"], emits: [knockNoted] }).decide(() => [
  emit(knockNoted, { knocked: true }),
]);

export const noteOpened = automation({ receives: { opened: sensor.opened }, commands: { noteOpen } }).send({});

export const noteKnocked = automation({ receives: { knocked: sensor.knocked }, commands: { noteKnock } }).send({});

export const bell = machine({
  description: "Decide on starting whether to ring; a settled machine never rests in starting, so no report moves it",
  commands: { ring: sensor.ring },
  initial: "starting",
  states: { starting: {}, ringing: {}, silent: {} },
}).chart({
  states: {
    starting: {
      always: [{ guard: { opened: ({ records }) => records.Door.opened }, target: "ringing" }, { target: "silent" }],
    },
    ringing: { sends: { ring: { onAccepted: [{ target: "silent" }], onRejected: [{ target: "silent" }] } } },
  },
});
