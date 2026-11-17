import type {
  DefinitionView,
  FlowEntry,
  Json,
  ScenarioView,
  ServiceView,
  StateView,
  TraceLine,
  ViewModel,
} from "@natsuzora-dev/tazuna/view";
import type { Viewport } from "@xyflow/react";
import type { ReactNode } from "react";
import { useEffect, useRef, useState } from "react";
import { activityText, Chart, type ChartPick, chartPick, transitionText } from "./Chart.tsx";
import type { Keeping } from "./diagram.tsx";
import { Er, type ErPick, erPick } from "./Er.tsx";
import { entryText, Flow } from "./Flow.tsx";
import { JsonView } from "./JsonView.tsx";
import { ServiceMap } from "./ServiceMap.tsx";

const tabs = ["services", "chart", "flow", "data"] as const;

interface Inspected {
  readonly id: string;
  readonly kind: string;
  readonly name: string;
  readonly value: Json | object;
}

function useHash(): string {
  const [hash, setHash] = useState(location.hash);
  useEffect(() => {
    const changed = () => setHash(location.hash);
    addEventListener("hashchange", changed);
    return () => removeEventListener("hashchange", changed);
  }, []);
  return hash;
}

const valueAt = (json: Json, path: readonly (string | number)[]): Json =>
  path.reduce<Json>((value, key) => (value as Readonly<Record<string, Json>>)[key] ?? null, json);

const statePath = (state: StateView) => state.path.flatMap((name) => ["states", name]);

function pickedJson(definition: DefinitionView, pick: ChartPick): Inspected {
  if (pick === null)
    return { id: definition.name, kind: definition.kind, name: definition.name, value: definition.definition };
  const at = (path: readonly (string | number)[]) => ({
    id: path.join("/"),
    value: valueAt(definition.definition, path),
  });
  if ("activity" in pick)
    return {
      kind: "activity",
      name: activityText(pick.activity),
      ...at([...statePath(pick.state), pick.activity.keyword, pick.activity.name]),
    };
  if ("transition" in pick)
    return {
      kind: "transition",
      name: transitionText(pick.transition),
      ...at([...statePath(pick.state), ...pick.transition.path, pick.transition.index]),
    };
  return { kind: "state", name: pick.state.name, ...at(statePath(pick.state)) };
}

function erJson(pick: ErPick): Inspected {
  const { definition } = pick.placed;
  if (pick.type === "entity")
    return { id: definition.name, kind: definition.kind, name: definition.name, value: definition.definition };
  return {
    id: `${definition.name}/${pick.field.name}/${pick.type}`,
    kind: pick.type,
    name: `${definition.name}.${pick.field.name}`,
    value: valueAt(definition.definition, ["fields", pick.field.name]),
  };
}

const serviceJson = (service: ServiceView): Inspected => ({
  id: service.name,
  kind: service.kind,
  name: service.name,
  value: service,
});

function ServiceList<T>({
  items,
  service,
  item,
}: {
  readonly items: readonly T[];
  readonly service: (item: T) => string;
  readonly item: (item: T) => ReactNode;
}) {
  return (
    <nav className="list">
      {[...Map.groupBy(items, service)].map(([name, group]) => (
        <section key={name}>
          <h2 className="kind">{name}</h2>
          {group.map(item)}
        </section>
      ))}
    </nav>
  );
}

const scenarioJson = (scenario: ScenarioView): Inspected => ({
  id: scenario.name,
  kind: "scenario",
  name: scenario.name,
  value: scenario,
});

function entryJson(scenario: ScenarioView, index: number): Inspected {
  const entry = scenario.entries[index] as FlowEntry;
  const line = scenario.trace?.[entry.line] as TraceLine;
  return { id: String(index), kind: line.type, name: entryText(entry, line), value: line };
}

export const LoadError = ({
  error,
  beside,
  diagrams,
}: {
  readonly error: string;
  /** Whether the tab has a list on the left, so that the section is placed to the right of the list. */
  readonly beside: boolean;
  readonly diagrams: boolean;
}) => (
  <section className={beside ? "load-error beside-list" : "load-error"} role="alert">
    <h2>{diagrams ? "spec not loaded. The diagrams show the last loaded spec" : "spec not loaded"}</h2>
    <pre>{error}</pre>
  </section>
);

const Notice = ({ text }: { readonly text: string }) => <p className="empty kind error">{text}</p>;

/**
 * The viewer page. A new model keeps the open tab, the pick if it still exists, and the viewport; the diagrams are
 * rebuilt and laid out again.
 */
export function App({
  model,
  version,
  error,
}: {
  readonly model: ViewModel;
  /** The model version; the diagrams are rebuilt when it changes. */
  readonly version: number;
  readonly error: string | null;
}) {
  const hash = useHash();
  const [hashTab, ...path] = hash.slice(1).split("/");
  const tab = tabs.find((t) => t === hashTab) ?? "services";
  const named = path[0] !== undefined;
  const charts = model.services.flatMap((service) =>
    service.definitions.flatMap((definition) =>
      definition.chart === null ? [] : [{ service: service.name, definition, root: definition.chart }],
    ),
  );
  const chart =
    tab === "chart"
      ? named
        ? charts.find((c) => c.service === path[0] && c.definition.name === path[1])
        : charts[0]
      : undefined;
  const scenario =
    tab === "flow"
      ? named
        ? model.scenarios.find((s) => s.service === path[0] && s.name === path[1])
        : model.scenarios[0]
      : undefined;
  const entityServices = model.services.filter((s) => s.definitions.some((d) => d.entity !== null));
  const dataService =
    tab === "data" ? (named ? entityServices.find((s) => s.name === path[0]) : entityServices[0]) : undefined;
  const missing =
    named && tab !== "services" && chart === undefined && scenario === undefined && dataService === undefined;
  const view =
    chart !== undefined
      ? `chart/${chart.service}/${chart.definition.name}`
      : scenario !== undefined
        ? `flow/${scenario.service}/${scenario.name}`
        : dataService !== undefined
          ? `data/${dataService.name}`
          : tab;
  const kept = useRef<{ readonly view: string; readonly viewport: Viewport } | null>(null);
  const keeping: Keeping = {
    kept: kept.current?.view === view ? kept.current.viewport : null,
    onMove: (viewport) => {
      kept.current = { view, viewport };
    },
  };
  const [selection, setSelection] = useState<{ readonly hash: string; readonly id: string } | null>(null);
  const selected = selection?.hash === hash ? selection.id : null;
  const pick = (id: string | null) => setSelection(id === null ? null : { hash, id });
  const resolved = ((): Inspected | undefined => {
    if (selected === null) return undefined;
    if (tab === "services") {
      const service = model.services.find((s) => s.name === selected);
      return service === undefined ? undefined : serviceJson(service);
    }
    if (chart !== undefined) {
      const picked = chartPick(chart.root, selected);
      return picked === undefined ? undefined : pickedJson(chart.definition, picked);
    }
    if (scenario !== undefined)
      return scenario.entries[Number(selected)] === undefined ? undefined : entryJson(scenario, Number(selected));
    if (dataService !== undefined) {
      const picked = erPick(model.services, dataService.name, selected);
      return picked === undefined ? undefined : erJson(picked);
    }
    return undefined;
  })();
  const picked = resolved === undefined ? null : selected;
  const diagram = `${view} ${version}`;
  const shown: Inspected =
    resolved ??
    (chart !== undefined
      ? pickedJson(chart.definition, null)
      : scenario !== undefined
        ? scenarioJson(scenario)
        : dataService !== undefined
          ? serviceJson(dataService)
          : { id: "", kind: "spec", name: model.spec, value: model });
  const crumbs =
    chart !== undefined
      ? [chart.service, chart.definition.name]
      : scenario !== undefined
        ? [scenario.service, scenario.name]
        : dataService !== undefined
          ? [dataService.name]
          : missing
            ? path
            : resolved !== undefined
              ? [resolved.name]
              : [];
  return (
    <div className="app">
      <header className="bar">
        <span className="brand">tazuna</span>
        <span className="crumbs">
          {[model.spec, ...crumbs.slice(0, -1)].join(" / ")}
          {crumbs.length > 0 && (
            <>
              {" / "}
              <b>{crumbs.at(-1)}</b>
            </>
          )}
        </span>
        <nav className="tabs">
          {tabs.map((name) => (
            <a key={name} href={`#${name}`} aria-current={name === tab ? "page" : undefined}>
              {name}
            </a>
          ))}
        </nav>
      </header>
      <div className="body">
        {tab === "services" && (
          <main className="canvas">
            <ServiceMap key={diagram} services={model.services} picked={picked} onPick={pick} {...keeping} />
          </main>
        )}
        {tab === "chart" && (
          <main className="canvas split">
            <ServiceList
              items={charts}
              service={(c) => c.service}
              item={(c) => (
                <a
                  key={c.definition.name}
                  href={`#chart/${c.service}/${c.definition.name}`}
                  aria-current={c === chart ? "page" : undefined}
                >
                  <span className={`chip c-${c.definition.kind}`}>{c.definition.kind}</span>
                  <span className="name">{c.definition.name}</span>
                </a>
              )}
            />
            {chart !== undefined && (
              <Chart
                key={diagram}
                chartKind={chart.definition.kind}
                root={chart.root}
                picked={picked}
                onPick={pick}
                {...keeping}
              />
            )}
            {missing && <Notice text={`${path.join("/")} not found`} />}
          </main>
        )}
        {tab === "flow" && (
          <main className="canvas split">
            <ServiceList
              items={model.scenarios}
              service={(s) => s.service}
              item={(s) => (
                <a
                  key={s.name}
                  href={`#flow/${s.service}/${s.name}`}
                  aria-current={s === scenario ? "page" : undefined}
                >
                  <span className="name">{s.name}</span>
                  {s.error !== null && <span className="kind error">error</span>}
                  {s.trace === null && s.error === null && <span className="kind">no snapshot</span>}
                </a>
              )}
            />
            {scenario !== undefined &&
              (scenario.trace !== null ? (
                <Flow
                  key={diagram}
                  scenario={scenario}
                  trace={scenario.trace}
                  picked={picked === null ? null : Number(picked)}
                  onPick={(index) => pick(index === null ? null : String(index))}
                  {...keeping}
                />
              ) : scenario.error !== null ? (
                <JsonView key={`${scenario.service}/${scenario.name}`} value={scenario.error} />
              ) : (
                <p className="empty kind">no snapshot. tazuna test --depth &lt;n&gt; --update writes it</p>
              ))}
            {missing && <Notice text={`${path.join("/")} not found`} />}
          </main>
        )}
        {tab === "data" && (
          <main className="canvas split">
            <nav className="list">
              {entityServices.map((s) => (
                <a key={s.name} href={`#data/${s.name}`} aria-current={s === dataService ? "page" : undefined}>
                  <span className="name">{s.name}</span>
                </a>
              ))}
            </nav>
            {dataService !== undefined && (
              <Er
                key={diagram}
                services={model.services}
                service={dataService.name}
                picked={picked}
                onPick={pick}
                {...keeping}
              />
            )}
            {missing && <Notice text={`${path.join("/")} not found`} />}
          </main>
        )}
        {error !== null && <LoadError error={error} beside={tab !== "services"} diagrams />}
        <aside className="inspect">
          <div className="title">
            <span className="kind">{shown.kind}</span>
            <span className="name">{shown.name}</span>
          </div>
          <JsonView key={`${hash} ${shown.id}`} value={shown.value} />
        </aside>
      </div>
    </div>
  );
}
