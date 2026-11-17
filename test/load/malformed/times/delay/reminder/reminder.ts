import { constants, duration, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine } = service({ description: "Remind after a while" });

export const reminderConstants = constants(z.object({ remindAfter: duration, nudgeAfter: duration }), {
  remindAfter: "P1D",
  nudgeAfter: "PT0.0005S",
});

export const reminder = machine({
  description: "Remind a day after it starts, and nudge half a millisecond after that",
  initial: "waiting",
  states: { waiting: { after: ["day"] }, reminding: { after: ["nudge"] }, done: {} },
}).chart({
  states: {
    waiting: { after: { day: { delay: reminderConstants.remindAfter, onFired: [{ target: "reminding" }] } } },
    reminding: { after: { nudge: { delay: reminderConstants.nudgeAfter, onFired: [{ target: "done" }] } } },
  },
});
