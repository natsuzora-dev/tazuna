import { createRoot } from "react-dom/client";
import "@xyflow/react/dist/base.css";
import "./tokens.css";
import "./style.css";
import type { ViewEvent, ViewModel } from "@natsuzora-dev/tazuna/view";
import { useEffect, useState } from "react";
import { App, LoadError } from "./App.tsx";

/** Returns the model, or null while model.json is 404, which it is until the spec has loaded once. */
const fetchModel = async (): Promise<ViewModel | null> => {
  const response = await fetch("./model.json");
  return response.ok ? response.json() : null;
};

function Live() {
  const [loaded, setLoaded] = useState<{ readonly model: ViewModel | null; readonly version: number }>({
    model: null,
    version: 0,
  });
  const [error, setError] = useState<string | null>(null);
  useEffect(() => {
    const events = new EventSource("./events");
    // Clear the error before the fetch: clearing after it would also drop an error that arrived during the fetch.
    const reload = async () => {
      setError(null);
      const model = await fetchModel();
      if (model !== null) setLoaded(({ version }) => ({ model, version: version + 1 }));
    };
    reload();
    events.onopen = reload;
    events.onmessage = (message) => {
      const event: ViewEvent = JSON.parse(message.data);
      if (event.type === "error") setError(event.message);
      else reload();
    };
    return () => events.close();
  }, []);
  if (loaded.model !== null) return <App model={loaded.model} version={loaded.version} error={error} />;
  return (
    <div className="app">
      <header className="bar">
        <span className="brand">tazuna</span>
      </header>
      <div className="body">{error !== null && <LoadError error={error} beside={false} diagrams={false} />}</div>
    </div>
  );
}

createRoot(document.getElementById("root") as HTMLElement).render(<Live />);
