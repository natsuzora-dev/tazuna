import type { StandardRPCCustomJsonSerializer } from "@orpc/client/standard";
import { z } from "zod";

const instant: StandardRPCCustomJsonSerializer = {
  type: 21,
  condition: (data) => data instanceof Temporal.Instant,
  serialize: (data: Temporal.Instant) => data.toString(),
  deserialize: (serialized) => Temporal.Instant.from(z.string().parse(serialized)),
};

export const customJsonSerializers = [instant];
