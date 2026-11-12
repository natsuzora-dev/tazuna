import { consumeEventIterator } from "@orpc/client";
import { useEffect, useEffectEvent } from "react";

export function useEvents<T>(
  subscribe: () => Promise<AsyncIteratorObject<T, unknown, void>>,
  onEvent: (event: T) => void,
): void {
  const onEachEvent = useEffectEvent(onEvent);
  useEffect(() => {
    let isCancelled = false;
    const cancel = consumeEventIterator(subscribe(), {
      onEvent: onEachEvent,
      // cancel fails the pending read with an AbortError.
      onError: (error) => {
        if (!isCancelled) throw error;
      },
    });
    return () => {
      isCancelled = true;
      void cancel();
    };
  }, [subscribe]);
}
