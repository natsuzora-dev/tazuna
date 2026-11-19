import { datetime, emit, service, singleEntity } from "@natsuzora-dev/tazuna";

export const Setting = singleEntity({
  description: "When the waiter pongs",
  fields: { due: datetime.nullable().default(null) },
});

export const { automation, command, machine, event, updateEvent, contract, given, scenario } = service({
  name: "sender",
  description: "Pong at the time that the setting holds",
  entities: { Setting },
});

export const armed = event({});
export const dueChanged = updateEvent({ entity: Setting, writes: ["due"] });
export const dueSet = event({});
export const ponged = event({});

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const setDue = command({ emits: [dueChanged, dueSet] }).decide(() => [
  emit(dueChanged, { due: Temporal.Instant.from("2026-10-24T00:00:00Z") }),
  emit(dueSet, {}),
]);

export const pong = command({ emits: [ponged] }).decide(() => [emit(ponged, {})]);

export const setDueOnArm = automation({ receives: { armed }, commands: { setDue } }).send({});

export const waiter = machine({
  description: "Pong at the setting's due, entering waiting again whenever the due changes",
  receives: { dueChanged },
  commands: { pong },
  initial: "waiting",
  states: { waiting: {}, ponging: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: { dueChanged: [{ target: "waiting", reenter: true }] },
      after: {
        due: {
          at: ({ records }) => records.Setting.due ?? Temporal.Instant.from("2099-01-01T00:00:00Z"),
          onFired: [{ target: "ponging" }],
        },
      },
    },
    ponging: { sends: { pong: { input: () => ({}), onAccepted: [{ target: "done" }] } } },
  },
});

export const sender = contract({ arm, dueSet, ponged });
