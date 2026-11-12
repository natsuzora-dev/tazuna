export function pushedStream<T>(request: Request) {
  const queued: T[] = [];
  let wake = Promise.withResolvers<void>();
  request.signal.addEventListener("abort", () => wake.resolve(), { once: true });
  return {
    values: (async function* () {
      while (!request.signal.aborted) {
        await wake.promise;
        wake = Promise.withResolvers<void>();
        yield* queued.splice(0);
      }
    })(),
    push(value: T) {
      queued.push(value);
      wake.resolve();
    },
  };
}

export const keepOpen = <T>(call: {
  readonly request: Request;
  readonly answer: (values: AsyncGenerator<T>) => void;
}) => call.answer(pushedStream<T>(call.request).values);
