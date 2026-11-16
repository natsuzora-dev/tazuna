import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Tag = entity({ description: "A tag", fields: { id: z.string() }, key: "id" });

export const { command, createEvent } = service({ description: "Keep tags", entities: { Tag } });

export const tagAdded = createEvent({ entity: Tag });

export const addTag = command({ input: { tagId: Tag.fields.id }, emits: [tagAdded] }).decide(({ input }) => [
  emit(tagAdded, { id: input.tagId }),
]);
