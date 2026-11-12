import { service } from "@natsuzora-dev/tazuna";

export const { screen } = service({ description: "Show the home screen only after signing in" });

export const homeScreen = screen({
  description: "The home screen, which no screen opens, so nothing gives the input that requires would read",
  initial: "showing",
  states: { showing: {} },
  requires: { signedIn: () => false },
}).chart({});
