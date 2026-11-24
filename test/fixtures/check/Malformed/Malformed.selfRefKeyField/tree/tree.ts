import { entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Node = entity({ description: "A node", fields: { id: ref.self() }, key: "id" });

export const Edge = entity({
  description: "An edge from a node",
  fields: { from: ref.self(), label: z.string() },
  key: ["from", "label"],
});

export const { bounds } = service({ name: "tree", description: "Keep the tree", entities: { Node, Edge } });
