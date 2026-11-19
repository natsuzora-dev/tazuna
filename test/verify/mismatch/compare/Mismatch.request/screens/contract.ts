import { ref } from "@natsuzora-dev/tazuna";
import { contract, Draft } from "./data.ts";

export const screens = contract({ DraftId: ref(Draft) });
