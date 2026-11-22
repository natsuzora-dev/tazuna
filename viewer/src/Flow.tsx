import type { FlowEntry, ScenarioView, TraceLine } from "@natsuzora-dev/tazuna/view";
import {
  Background,
  BaseEdge,
  Controls,
  type Edge,
  type EdgeProps,
  Handle,
  type Node,
  type NodeProps,
  Position,
  ReactFlow,
  ReactFlowProvider,
  useNodesInitialized,
  useNodesState,
  useReactFlow,
  useStore,
} from "@xyflow/react";
import { createContext, type MouseEvent, useContext, useEffect, useState } from "react";
import {
  ArrowDefs,
  arrowMarker,
  cssPx,
  type Keeping,
  openArrowMarker,
  type Point,
  useFirstViewport,
} from "./diagram.tsx";
import { lineTones } from "./tone.ts";

type MessageEntry = Exclude<FlowEntry, { type: "time" }>;

function messageText(entry: MessageEntry, l: Exclude<TraceLine, { type: "time" }>): string {
  if (l.type === "answer")
    return [l.to, l.answer.result, l.answer.result === "rejected" ? l.answer.rejection.kind : undefined]
      .filter((part) => part !== undefined)
      .join(" ");
  if (l.type === "unsubscribe") return `unsubscribe ${l.to}`;
  if (l.type === "restart") return "restart";
  if (l.type === "operation") return l.name;
  const name = entry.to !== null && l.name.startsWith(`${entry.to}.`) ? l.name.slice(entry.to.length + 1) : l.name;
  return [l.type === "subscribe" ? "subscribe" : undefined, name, l.id].filter((p) => p !== undefined).join(" ");
}

export const entryText = (entry: FlowEntry, l: TraceLine) =>
  entry.type === "time" || l.type === "time" ? new Date(l.time).toISOString() : messageText(entry, l);

interface Picking {
  readonly picked: number | null;
  readonly pick: (index: number | null) => void;
}
const PickingContext = createContext<Picking>({ picked: null, pick: () => {} });

interface StepData extends Record<string, unknown> {
  readonly entry: FlowEntry;
  readonly index: number;
  readonly line: TraceLine;
}
type HeadNode = Node<{ readonly name: string }, "head">;
type HeadBackdropNode = Node<Record<string, never>, "headBackdrop">;
type LabelNode = Node<StepData, "label">;
type TimeNode = Node<StepData, "time">;
type FlowNode = HeadNode | HeadBackdropNode | LabelNode | TimeNode;
type LineLook = "lifeline" | "timeRule" | "call" | "answer";
type FlowEdge = Edge<
  { readonly points: readonly Point[]; readonly look: LineLook; readonly index: number | null },
  "line"
>;

const layers = { headBackdrop: 1, head: 2 } as const;

/**
 * Returns the offset of the headers in diagram coordinates. React Flow moves the diagram with a transform, so CSS
 * sticky cannot pin the headers.
 */
function useHeadOffset(): number {
  const [, y, zoom] = useStore((s) => s.transform);
  return Math.max(0, (cssPx("--space-edge") - y) / zoom);
}

function Head({ data: { name } }: NodeProps<HeadNode>) {
  const offset = useHeadOffset();
  return (
    <div className="lifeline-head box" style={{ transform: `translateY(${offset}px)` }}>
      <Handle type="target" position={Position.Bottom} isConnectable={false} />
      {name}
      <Handle type="source" position={Position.Bottom} isConnectable={false} />
    </div>
  );
}

function HeadBackdrop() {
  const offset = useHeadOffset();
  const [x, , zoom] = useStore((s) => s.transform);
  const width = useStore((s) => s.width);
  const head = useStore((s) => s.nodeLookup.get(headId(0))?.measured.height ?? 0);
  if (offset === 0) return null;
  const edge = cssPx("--space-edge") / zoom;
  return (
    <div
      className="head-backdrop"
      style={{
        transform: `translate(${-x / zoom}px, ${offset - edge}px)`,
        width: width / zoom,
        height: edge + head + cssPx("--space-part") / zoom,
      }}
    />
  );
}

function usePick(index: number) {
  const { picked, pick } = useContext(PickingContext);
  const onClick = (e: MouseEvent) => {
    e.stopPropagation();
    pick(index);
  };
  return { pressed: picked === index, onClick };
}

function Label({ data: { entry, index, line } }: NodeProps<LabelNode>) {
  const { pressed, onClick } = usePick(index);
  return (
    <button type="button" className={`label t-${lineTones[line.type]}`} aria-pressed={pressed} onClick={onClick}>
      {entryText(entry, line)}
    </button>
  );
}

function Time({ data: { index, line } }: NodeProps<TimeNode>) {
  const { pressed, onClick } = usePick(index);
  return (
    <button type="button" className="time" aria-pressed={pressed} onClick={onClick}>
      {new Date(line.time).toISOString()}
    </button>
  );
}

const markers: Readonly<Partial<Record<LineLook, string>>> = { call: arrowMarker, answer: openArrowMarker };

function Line({ id, data }: EdgeProps<FlowEdge>) {
  const { picked } = useContext(PickingContext);
  const [from, to] = data?.points ?? [];
  if (data === undefined || from === undefined || to === undefined) return null;
  const marker = markers[data.look];
  return (
    <BaseEdge
      id={id}
      className={data.index !== null && data.index === picked ? `${data.look} picked` : data.look}
      path={`M ${from.x} ${from.y} L ${to.x} ${to.y}`}
      {...(marker === undefined ? {} : { markerEnd: marker })}
      interactionWidth={data.index === null ? 0 : cssPx("--space-part")}
    />
  );
}

const nodeTypes = { head: Head, headBackdrop: HeadBackdrop, label: Label, time: Time };
const edgeTypes = { line: Line };
/** The minimum zoom. Fitting a wide trace can need less than React Flow's default minZoom of 0.5. */
const minZoom = 0.1;

const columns = (scenario: ScenarioView): readonly (string | null)[] => [null, ...scenario.lifelines];
const headId = (column: number) => `head:${column}`;
const labelId = (index: number) => `label:${index}`;
const timeId = (index: number) => `time:${index}`;

function flowNodes(scenario: ScenarioView, trace: readonly TraceLine[]): FlowNode[] {
  const at = { x: 0, y: 0 };
  return [
    ...columns(scenario).map(
      (name, column): HeadNode => ({
        id: headId(column),
        type: "head",
        position: at,
        zIndex: layers.head,
        data: { name: name ?? "scenario" },
      }),
    ),
    {
      id: "headBackdrop",
      type: "headBackdrop",
      position: at,
      zIndex: layers.headBackdrop,
      selectable: false,
      data: {},
    },
    ...scenario.entries.flatMap((entry, index): FlowNode[] => {
      const line = trace[entry.line] as TraceLine;
      const previous = trace[scenario.entries[index - 1]?.line ?? -1];
      const data = { entry, index, line };
      const time: TimeNode[] =
        previous?.time !== line.time ? [{ id: timeId(index), type: "time", position: at, data }] : [];
      return entry.type === "time" ? time : [...time, { id: labelId(index), type: "label", position: at, data }];
    }),
  ];
}

interface Size {
  readonly width: number;
  readonly height: number;
}

/**
 * Returns the positions and lines of a sequence diagram. Each lifeline gap widens to fit both headers and the labels of
 * the arrows that cross it.
 */
function sequenceLayout(scenario: ScenarioView, trace: readonly TraceLine[], size: ReadonlyMap<string, Size>) {
  const cols = columns(scenario);
  const sizeOf = (id: string) => size.get(id) ?? { width: 0, height: 0 };
  const gap = cssPx("--space-node-gap");
  const pad = cssPx("--space-row");
  const gaps = cols.slice(1).map((_, c) => (sizeOf(headId(c)).width + sizeOf(headId(c + 1)).width) / 2 + gap);
  const columnOf = (p: string | null) => cols.indexOf(p);
  // A service's own event sits on its lifeline and widens no gap.
  scenario.entries.forEach((entry, index) => {
    if (entry.type === "time") return;
    const [a, b] = [columnOf(entry.from), columnOf(entry.to)].sort((x, y) => x - y) as [number, number];
    if (a === b) return;
    const span = gaps.slice(a, b).map((_, i) => a + i);
    const lack = sizeOf(labelId(index)).width + 2 * pad - span.reduce((sum, c) => sum + (gaps[c] ?? 0), 0);
    if (lack > 0) for (const c of span) gaps[c] = (gaps[c] ?? 0) + lack / span.length;
  });
  const xs = [gap + sizeOf(headId(0)).width / 2];
  for (const g of gaps) xs.push((xs.at(-1) ?? 0) + g);
  const headHeight = Math.max(...cols.map((_, c) => sizeOf(headId(c)).height));
  const labelHeight = Math.max(0, ...scenario.entries.map((_, i) => sizeOf(labelId(i)).height));
  const row = cssPx("--size-message-row");
  const inner = cssPx("--space-inner");
  const top = headHeight + cssPx("--space-edge");
  // A time change gets its own divider row, as in PlantUML; messages below it happen at that time.
  const slots = new Map<number, number>();
  const dividers = new Map<number, number>();
  let slot = 0;
  scenario.entries.forEach((entry, index) => {
    if (size.has(timeId(index))) dividers.set(index, slot++);
    if (entry.type !== "time") slots.set(index, slot++);
  });
  const arrowY = (index: number) => top + ((slots.get(index) ?? 0) + 1) * row - cssPx("--space-part");
  const labelY = (index: number) => arrowY(index) - inner - labelHeight;
  const dividerY = (index: number) => top + (dividers.get(index) ?? 0) * row + row / 2;
  const bottom = top + slot * row + cssPx("--space-edge");
  const positions = new Map<string, Point>();
  cols.forEach((_, c) => {
    const { width } = sizeOf(headId(c));
    positions.set(headId(c), { x: (xs[c] ?? 0) - width / 2, y: 0 });
  });
  const line = (id: string, look: LineLook, points: readonly Point[], index: number | null): FlowEdge => ({
    id,
    source: headId(0),
    target: headId(0),
    type: "line",
    data: { points, look, index },
  });
  const edges = cols.map((_, c) =>
    line(
      `lifeline:${c}`,
      "lifeline",
      [
        { x: xs[c] ?? 0, y: headHeight },
        { x: xs[c] ?? 0, y: bottom },
      ],
      null,
    ),
  );
  scenario.entries.forEach((entry, index) => {
    if (entry.type === "time") return;
    const y = arrowY(index);
    const label = sizeOf(labelId(index));
    const [from, to] = [columnOf(entry.from), columnOf(entry.to)];
    const [x1, x2] = [xs[from] ?? 0, xs[to] ?? 0];
    if (from === to) {
      positions.set(labelId(index), { x: x1 - label.width / 2, y: labelY(index) });
      return;
    }
    positions.set(labelId(index), { x: (x1 + x2) / 2 - label.width / 2, y: labelY(index) });
    const look = trace[entry.line]?.type === "answer" ? "answer" : "call";
    edges.push(
      line(
        `message:${index}`,
        look,
        [
          { x: x1, y },
          { x: x2, y },
        ],
        index,
      ),
    );
  });
  const right = Math.max(...[...positions].map(([id, at]) => at.x + sizeOf(id).width)) + gap;
  for (const index of dividers.keys()) {
    const time = sizeOf(timeId(index));
    const y = dividerY(index);
    const x = right / 2 - time.width / 2;
    positions.set(timeId(index), { x, y: y - time.height / 2 });
    for (const [side, points] of [
      [
        "left",
        [
          { x: 0, y },
          { x: x - pad, y },
        ],
      ],
      [
        "right",
        [
          { x: x + time.width + pad, y },
          { x: right, y },
        ],
      ],
    ] as const)
      edges.unshift(line(`timeRule:${index}:${side}`, "timeRule", points, null));
  }
  return { positions, edges, width: right };
}

interface FlowProps extends Keeping {
  readonly scenario: ScenarioView;
  readonly trace: readonly TraceLine[];
  /** The picked entry, as an index into ScenarioView.entries. */
  readonly picked: number | null;
  readonly onPick: (index: number | null) => void;
}

function Diagram({ scenario, trace, picked, onPick: pick, kept, onMove }: FlowProps) {
  const [nodes, setNodes, onNodesChange] = useNodesState<FlowNode>(flowNodes(scenario, trace));
  const [edges, setEdges] = useState<FlowEdge[]>([]);
  const [laidOut, setLaidOut] = useState(false);
  const [diagramWidth, setDiagramWidth] = useState(0);
  const measured = useNodesInitialized();
  const { setViewport } = useReactFlow();
  const width = useStore((s) => s.width);
  useEffect(() => {
    if (!measured || laidOut) return;
    const size = new Map(nodes.map((n) => [n.id, { width: n.measured?.width ?? 0, height: n.measured?.height ?? 0 }]));
    const layout = sequenceLayout(scenario, trace, size);
    setNodes((current) => current.map((n) => ({ ...n, position: layout.positions.get(n.id) ?? n.position })));
    setEdges(layout.edges);
    setDiagramWidth(layout.width);
    setLaidOut(true);
  }, [measured, laidOut, nodes, scenario, trace, setNodes]);
  const shown = useFirstViewport(laidOut, kept, () => {
    const pad = cssPx("--space-edge");
    const zoom = Math.min(1, (width - 2 * pad) / diagramWidth);
    return setViewport({ x: Math.max(pad, (width - diagramWidth * zoom) / 2), y: pad, zoom });
  });
  return (
    <PickingContext.Provider value={{ picked, pick }}>
      <ReactFlow
        className={shown ? undefined : "pending"}
        nodes={nodes}
        edges={edges}
        nodeTypes={nodeTypes}
        edgeTypes={edgeTypes}
        onNodesChange={onNodesChange}
        onEdgeClick={(_, edge) => {
          const index = edge.data?.index;
          if (typeof index === "number") pick(index);
        }}
        onPaneClick={() => pick(null)}
        onMove={(_, viewport) => onMove(viewport)}
        onNodeClick={(_, node) => {
          if (node.type === "head") pick(null);
        }}
        panOnScroll
        minZoom={minZoom}
        nodesDraggable={false}
        nodesConnectable={false}
        elementsSelectable={false}
        edgesFocusable={false}
      >
        <ArrowDefs />
        <Background gap={cssPx("--space-edge")} size={cssPx("--size-dot") * 2} />
        <Controls showInteractive={false} />
      </ReactFlow>
    </PickingContext.Provider>
  );
}

export function Flow(props: FlowProps) {
  return (
    <ReactFlowProvider>
      <Diagram {...props} />
    </ReactFlowProvider>
  );
}
