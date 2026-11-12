import { contract } from "@natsuzora-dev/tazuna";
import { pause, play, queueTrack, skip } from "./player.ts";

export const player = contract({ queueTrack, play, skip, pause });
