import { domain, explore } from "@natsuzora-dev/tazuna";
import { invite, note } from "./club.ts";

export const clubExplore = explore({
  service: "club",
  depth: 2,
  domains: [domain(note.input.text, ["one"]), domain(invite.input.email, ["ann@example.com"])],
});
