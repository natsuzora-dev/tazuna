import type { Clock } from "./clock.ts";
import type { Service } from "./service.ts";

/**
 * Delivers each service's published events to the services that consume them, at least once, until no outbox holds
 * an unpublished event. A delivery that throws leaves its event unpublished for the next run.
 */
export function createRelay(services: readonly Service[], clock: Clock) {
  let running: Promise<void> | undefined;
  let again = false;

  async function drain() {
    for (let delivered = true; delivered; ) {
      delivered = false;
      for (const from of services) {
        for (const message of from.outbox.unpublished()) {
          for (const to of services) {
            if (to !== from && to.subscribes.includes(message.type)) await to.handle(message);
          }
          from.outbox.markPublished([message.id], clock.now());
          delivered = true;
        }
      }
    }
  }

  return {
    /** Runs a delivery round soon, or once more after the one in progress. */
    schedule(): void {
      if (running) {
        again = true;
        return;
      }
      running = (async () => {
        do {
          again = false;
          await drain().catch((error) => console.error("event delivery failed", error));
        } while (again);
        running = undefined;
      })();
    },
    /** Resolves when no delivery round is running. */
    async settled(): Promise<void> {
      while (running) await running;
    },
  };
}
