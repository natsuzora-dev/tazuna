import { EventPublisher } from "@orpc/server";

export const changes = new EventPublisher<{ changed: undefined }>();

export function notifyChange(): void {
  changes.publish("changed", undefined);
}
