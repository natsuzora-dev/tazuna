import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Memo = entity({ description: "A memo", fields: { id: z.string() }, key: "id" });

export const { event } = service({ description: "Keep the memos", entities: { Memo } });

export const memoWritten = event({});
