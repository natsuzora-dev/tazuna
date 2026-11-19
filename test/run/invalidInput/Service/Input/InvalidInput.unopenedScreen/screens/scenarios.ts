import { confirmDialog, given, listScreen, scenario } from "./screens.ts";

const arranged = given({ start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] });

export const cancelUnopened = scenario({
  description:
    "Cancel the dialog twice; the first cancel closes it, so the second operates a screen that is not open, and test reports unopenedScreen",
  given: arranged,
  when: (w) => {
    const dialog = w.user.operate(w.startup.screen(listScreen), "clear").screen(confirmDialog);
    w.user.operate(dialog, "cancel");
    w.user.operate(dialog, "cancel");
  },
  then: () => [],
});
