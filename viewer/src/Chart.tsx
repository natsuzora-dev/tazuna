import type { ActivityView, DefinitionView, StateView, TransitionView, Trigger } from "@natsuzora-dev/tazuna/view";
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
  useEdgesState,
  useNodesInitialized,
  useNodesState,
  useReactFlow,
  useStore,
} from "@xyflow/react";
import type { ElkExtendedEdge, ElkNode } from "elkjs/lib/elk-api.js";
import { createContext, type MouseEvent, useContext, useEffect, useState } from "react";
import {
  ArrowDefs,
  arrowMarker,
  cssPx,
  edgePoints,
  elk,
  type Keeping,
  type Point,
  roundedPath,
  useFirstViewport,
} from "./diagram.tsx";
import type { Tone } from "./tone.ts";

export type ChartPick =
  | { readonly state: StateView }
  | { readonly state: StateView; readonly transition: TransitionView }
  | { readonly state: StateView; readonly activity: ActivityView }
  | null;

const stateId = (state: StateView) => `state:${state.path.join("/")}`;
const initialId = (state: StateView) => `initial:${state.path.join("/")}`;
const transitionId = (t: TransitionView) => `transition:${t.id}`;
const labelId = (t: TransitionView) => `label:${t.id}`;
const activityId = (state: StateView, r: ActivityView) => `activity:${state.path.join("/")}/${r.keyword}/${r.name}`;

export function transitionText(t: TransitionView): string {
  const trigger = (tr: Trigger) => {
    if (tr.type === "event" || tr.type === "control") return tr.name;
    if (tr.type === "after") return `after ${tr.deadline}`;
    if (tr.type === "answer") return `${tr.name}.${tr.answer}`;
    return tr.type;
  };
  return [trigger(t.trigger), ...(t.guards.length === 0 ? [] : [`[${t.guards.join(", ")}]`])].join(" ");
}

/**
 * Returns the UML internal activity notation of an activity: `shows` runs while in the state (do), the others on entry.
 */
export const activityText = (r: ActivityView) => `${r.keyword === "shows" ? "do" : "entry"} / ${r.keyword} ${r.name}`;

function labelTone(trigger: Trigger): Tone {
  if (trigger.type === "answer") return trigger.kind;
  return trigger.type;
}

interface Picking {
  readonly picked: string | null;
  readonly pick: (id: string | null) => void;
}
const PickingContext = createContext<Picking>({ picked: null, pick: () => {} });

function usePick(id: string) {
  const { picked, pick } = useContext(PickingContext);
  const onClick = (e: MouseEvent) => {
    e.stopPropagation();
    pick(id);
  };
  return { pressed: picked === id, onClick };
}

function EdgeLabel({ data: { transition } }: NodeProps<LabelNode>) {
  const { pressed, onClick } = usePick(transitionId(transition));
  return (
    <button
      type="button"
      className={`label t-${labelTone(transition.trigger)}`}
      aria-pressed={pressed}
      onClick={onClick}
    >
      {transitionText(transition)}
      {transition.reenter && <span className="reenter"> reenter</span>}
    </button>
  );
}

function ActivityLine({ state, activity }: { readonly state: StateView; readonly activity: ActivityView }) {
  const { pressed, onClick } = usePick(activityId(state, activity));
  return (
    <button type="button" className="line" aria-pressed={pressed} onClick={onClick}>
      <span className={`mark m-${activity.kind}`} />
      {activityText(activity)}
    </button>
  );
}

function InternalLine({ transition }: { readonly transition: TransitionView }) {
  const { pressed, onClick } = usePick(transitionId(transition));
  return (
    <button type="button" className="line" aria-pressed={pressed} onClick={onClick}>
      {transitionText(transition)}
      {transition.reenter && <span className="reenter"> reenter</span>}
    </button>
  );
}

interface StateData extends Record<string, unknown> {
  readonly state: StateView;
  readonly chartKind: DefinitionView["kind"] | null;
  readonly region: boolean;
}
type StateNode = Node<StateData, "state">;
type InitialNode = Node<Record<string, never>, "initial">;
type LabelNode = Node<{ readonly transition: TransitionView }, "label">;
type ChartNode = StateNode | InitialNode | LabelNode;
type TransitionEdge = Edge<
  { readonly points: readonly Point[]; readonly transition: TransitionView | null },
  "transition"
>;

function StateBox({ id, data: { state, chartKind, region } }: NodeProps<StateNode>) {
  const { picked } = useContext(PickingContext);
  const internal = state.transitions.filter((t) => t.target === null);
  const classes = [
    "state",
    state.states.length > 0 ? "group" : "box",
    region ? "region" : "",
    state.kind,
    picked === id ? "picked" : "",
  ];
  return (
    <div className={classes.filter((c) => c !== "").join(" ")}>
      <Handle type="target" position={Position.Left} isConnectable={false} />
      <div className="head">
        <div className="state-title">
          {chartKind !== null && <span className="kind">{chartKind}</span>}
          <span className="state-name">
            {state.kind === "history" && <span className="history-mark">H</span>}
            {state.name}
            {(state.kind === "parallel" || state.kind === "map") && <span className="kind"> {state.kind}</span>}
          </span>
        </div>
        {(state.activities.length > 0 || internal.length > 0) && (
          <div className="compartment">
            {state.activities.map((r) => (
              <ActivityLine key={activityId(state, r)} state={state} activity={r} />
            ))}
            {internal.map((t) => (
              <InternalLine key={transitionId(t)} transition={t} />
            ))}
          </div>
        )}
      </div>
      <Handle type="source" position={Position.Right} isConnectable={false} />
    </div>
  );
}

function InitialDot() {
  return (
    <div className="initial">
      <Handle type="source" position={Position.Right} isConnectable={false} />
    </div>
  );
}

function TransitionLine({ id, data }: EdgeProps<TransitionEdge>) {
  const { picked } = useContext(PickingContext);
  return (
    <BaseEdge
      id={id}
      className={picked === id ? "picked" : undefined}
      path={roundedPath(data?.points ?? [], cssPx("--radius-corner"))}
      markerEnd={arrowMarker}
      interactionWidth={cssPx("--space-part")}
    />
  );
}

/** The minimum zoom. fitView never zooms below it, and React Flow's default 0.5 cannot fit a wide chart. */
const minZoom = 0.1;
const nodeTypes = { state: StateBox, initial: InitialDot, label: EdgeLabel };
const edgeTypes = { transition: TransitionLine };

const allStates = (state: StateView): StateView[] => [state, ...state.states.flatMap(allStates)];

export function chartPick(root: StateView, id: string): Exclude<ChartPick, null> | undefined {
  for (const state of allStates(root)) {
    if (state !== root && stateId(state) === id) return { state };
    const activity = state.activities.find((r) => activityId(state, r) === id);
    if (activity !== undefined) return { state, activity };
    const transition = state.transitions.find((t) => transitionId(t) === id);
    if (transition !== undefined) return { state, transition };
  }
  return undefined;
}
const depthOf = (state: StateView) => state.path.length;
const lineZ = (root: StateView) => Math.max(...allStates(root).map(depthOf)) + 1;

function chartNodes(chartKind: DefinitionView["kind"], root: StateView): ChartNode[] {
  const walk = (state: StateView, parent: StateView | null): ChartNode[] => [
    {
      id: stateId(state),
      type: "state",
      position: { x: 0, y: 0 },
      zIndex: depthOf(state),
      ...(parent === null ? {} : { parentId: stateId(parent) }),
      data: { state, chartKind: parent === null ? chartKind : null, region: parent?.kind === "parallel" },
    },
    ...(state.initial === null
      ? []
      : [
          {
            id: initialId(state),
            type: "initial" as const,
            position: { x: 0, y: 0 },
            zIndex: depthOf(state) + 1,
            parentId: stateId(state),
            data: {},
          },
        ]),
    ...state.states.flatMap((child) => walk(child, state)),
  ];
  const labels = allStates(root).flatMap((state) =>
    state.transitions
      .filter((t) => t.target !== null)
      .map(
        (transition): LabelNode => ({
          id: labelId(transition),
          type: "label",
          position: { x: 0, y: 0 },
          zIndex: lineZ(root) + 1,
          data: { transition },
        }),
      ),
  );
  return [...walk(root, null), ...labels];
}

interface Line {
  readonly id: string;
  readonly source: string;
  readonly target: string;
  readonly from: StateView | null;
  readonly to: StateView;
  readonly transition: TransitionView | null;
}

const contains = (outer: StateView, inner: StateView) =>
  inner.path.length > outer.path.length && outer.path.every((key, i) => inner.path[i] === key);

function chartLines(root: StateView): Line[] {
  const states = allStates(root);
  const byName = new Map(states.filter((s) => s !== root).map((s) => [s.name, s]));
  return states.flatMap((state) => [
    ...(state.initial === null
      ? []
      : [
          {
            id: `${initialId(state)}>`,
            source: initialId(state),
            target: stateId(byName.get(state.initial) as StateView),
            from: null,
            to: byName.get(state.initial) as StateView,
            transition: null,
          },
        ]),
    ...state.transitions.flatMap((t) => {
      if (t.target === null) return [];
      const to = byName.get(t.target) as StateView;
      return [{ id: transitionId(t), source: stateId(state), target: stateId(to), from: state, to, transition: t }];
    }),
  ]);
}

const directions = ["RIGHT", "DOWN"] as const;
type Direction = (typeof directions)[number];
const sides = { RIGHT: { input: "WEST", output: "EAST" }, DOWN: { input: "NORTH", output: "SOUTH" } } as const;
type Side = (typeof sides)[Direction][keyof (typeof sides)[Direction]];

interface Box {
  readonly x: number;
  readonly y: number;
  readonly width: number;
  readonly height: number;
}

interface Joint {
  readonly id: string;
  readonly port: { readonly state: string; readonly side: Side } | null;
}

interface Chain {
  readonly joints: readonly Joint[];
  readonly labelAt: number;
}

/**
 * Returns the joints of a line. ELK cannot lay out an edge without a port that crosses the border of a state with fixed
 * port sides, so every border crossing gets its own port. ELK enters a compound state on its input side, so an edge
 * from a state beyond the output side loops around the diagram; the first layout finds such edges, and they enter on
 * the output side.
 */
function lineChain(
  line: Line,
  states: readonly StateView[],
  direction: Direction,
  boxes: ReadonlyMap<string, Box> | null,
): Chain {
  const { from, to } = line;
  const node = (id: string): Joint => ({ id, port: null });
  if (from === null) return { joints: [node(line.source), node(line.target)], labelAt: 0 };
  const { input, output } = sides[direction];
  const port = (state: StateView, side: Side): Joint => ({
    id: `port:${side}:${stateId(state)}:${line.id}`,
    port: { state: stateId(state), side },
  });
  const ancestorsInnermostFirst = (inner: StateView) =>
    states.filter((s) => contains(s, inner)).sort((a, b) => b.path.length - a.path.length);
  const source = boxes?.get(line.source);
  const beyondOutput = (state: StateView) => {
    const outer = boxes?.get(stateId(state));
    if (outer === undefined || source === undefined) return false;
    return direction === "DOWN"
      ? source.y + source.height / 2 > outer.y + outer.height
      : source.x + source.width / 2 > outer.x + outer.width;
  };
  const start = contains(from, to) ? port(from, input) : node(line.source);
  const exited = ancestorsInnermostFirst(from).filter((s) => s !== to && !contains(s, to));
  const enteredOutermostFirst = ancestorsInnermostFirst(to)
    .filter((s) => s !== from && !contains(s, from))
    .reverse();
  const entersGroupFromOutside = to.states.length > 0 && !contains(to, from);
  const end = entersGroupFromOutside && beyondOutput(to) ? port(to, output) : node(line.target);
  return {
    joints: [
      start,
      ...exited.map((s) => port(s, output)),
      ...enteredOutermostFirst.map((s) => port(s, beyondOutput(s) ? output : input)),
      end,
    ],
    // The piece after the last exit port is the outermost one.
    labelAt: exited.length,
  };
}

const pieceId = (line: Line, i: number) => `${line.id}#${i}`;

function chartGraph(
  root: StateView,
  lines: readonly Line[],
  chains: ReadonlyMap<string, Chain>,
  size: ReadonlyMap<string, { readonly width: number; readonly height: number }>,
  direction: Direction,
): ElkNode {
  const spacing = {
    "elk.algorithm": "layered",
    "elk.direction": direction,
    "elk.edgeRouting": "ORTHOGONAL",
    "elk.layered.cycleBreaking.strategy": "DEPTH_FIRST",
    // Shorter, straighter edges than the default BRANDES_KOEPF.
    "elk.layered.nodePlacement.strategy": "NETWORK_SIMPLEX",
    "elk.spacing.nodeNode": String(cssPx("--space-node-gap")),
    "elk.layered.spacing.nodeNodeBetweenLayers": String(cssPx("--space-layer-gap")),
    "elk.spacing.edgeNode": String(cssPx("--space-row")),
    "elk.spacing.edgeEdge": String(cssPx("--space-part")),
    "elk.spacing.edgeLabel": String(cssPx("--space-inner")),
  };
  const pad = cssPx("--space-row");
  const ports = Map.groupBy(
    [...chains.values()].flatMap(({ joints }) =>
      joints.flatMap((j) => (j.port === null ? [] : [{ id: j.id, ...j.port }])),
    ),
    (port) => port.state,
  );
  const elkNode = (state: StateView): ElkNode => {
    const head = size.get(stateId(state)) ?? { width: 0, height: 0 };
    if (state.states.length === 0) return { id: stateId(state), ...head };
    const own = ports.get(stateId(state)) ?? [];
    return {
      id: stateId(state),
      layoutOptions: {
        ...spacing,
        "elk.padding": `[top=${head.height + pad},left=${pad},bottom=${pad},right=${pad}]`,
        "elk.nodeSize.constraints": "MINIMUM_SIZE",
        "elk.nodeSize.minimum": `(${head.width}, ${head.height})`,
        "elk.portConstraints": "FIXED_SIDE",
      },
      ports: own.map((port) => ({ id: port.id, layoutOptions: { "elk.port.side": port.side } })),
      children: [
        ...(state.initial === null ? [] : [{ id: initialId(state), ...size.get(initialId(state)) }]),
        ...state.states.map(elkNode),
      ],
    };
  };
  return {
    id: "chart",
    layoutOptions: { ...spacing, "elk.hierarchyHandling": "INCLUDE_CHILDREN", "elk.json.edgeCoords": "ROOT" },
    children: [elkNode(root)],
    edges: lines.flatMap((line) => {
      const { joints, labelAt } = chains.get(line.id) as Chain;
      return joints.slice(1).map(
        (target, i): ElkExtendedEdge => ({
          id: pieceId(line, i),
          sources: [(joints[i] as Joint).id],
          targets: [target.id],
          // ELK does not place a label without text.
          labels:
            line.transition === null || i !== labelAt
              ? []
              : [
                  {
                    id: labelId(line.transition),
                    text: transitionText(line.transition),
                    ...size.get(labelId(line.transition)),
                  },
                ],
        }),
      );
    }),
  };
}

function absoluteBoxes(laid: ElkNode): Map<string, Box> {
  const boxes = new Map<string, Box>();
  const walk = (n: ElkNode, x: number, y: number) => {
    const at = { x: x + (n.x ?? 0), y: y + (n.y ?? 0), width: n.width ?? 0, height: n.height ?? 0 };
    boxes.set(n.id, at);
    for (const child of n.children ?? []) walk(child, at.x, at.y);
  };
  for (const child of laid.children ?? []) walk(child, 0, 0);
  return boxes;
}

/**
 * Returns the points of a line. ELK puts a north port at the top of the box, so a line from inside the north border
 * starts below the header.
 */
function linePoints(
  line: Line,
  { joints }: Chain,
  laidEdges: ReadonlyMap<string, ElkExtendedEdge>,
  size: ReadonlyMap<string, { readonly height: number }>,
): Point[] {
  const points = joints
    .slice(1)
    .flatMap((_, i) => edgePoints(laidEdges.get(pieceId(line, i))))
    .filter((p, i, all) => i === 0 || p.x !== all[i - 1]?.x || p.y !== all[i - 1]?.y);
  const [start, ...rest] = points;
  const first = joints[0]?.port;
  const startsInsideTop = first?.state === line.source && first.side === "NORTH";
  if (start === undefined || !startsInsideTop) return points;
  return [{ x: start.x, y: start.y + (size.get(line.source)?.height ?? 0) }, ...rest];
}

interface ChartProps extends Keeping {
  readonly chartKind: DefinitionView["kind"];
  readonly root: StateView;
  readonly picked: string | null;
  readonly onPick: (id: string | null) => void;
}

function Diagram({ chartKind, root, picked, onPick, kept, onMove }: ChartProps) {
  const [nodes, setNodes, onNodesChange] = useNodesState<ChartNode>(chartNodes(chartKind, root));
  const [edges, setEdges, onEdgesChange] = useEdgesState<TransitionEdge>([]);
  const [laidOut, setLaidOut] = useState(false);
  const measured = useNodesInitialized();
  const { fitView } = useReactFlow();
  const width = useStore((s) => s.width);
  const height = useStore((s) => s.height);
  useEffect(() => {
    if (!measured || laidOut) return;
    const size = new Map(nodes.map((n) => [n.id, { width: n.measured?.width ?? 0, height: n.measured?.height ?? 0 }]));
    const lines = chartLines(root);
    const fit = (g: ElkNode) => Math.min(width / (g.width ?? 1), height / (g.height ?? 1));
    const states = allStates(root);
    const layout = async (direction: Direction) => {
      const chainsFrom = (boxes: ReadonlyMap<string, Box> | null) =>
        new Map(lines.map((line) => [line.id, lineChain(line, states, direction, boxes)]));
      const first = await elk.layout(chartGraph(root, lines, chainsFrom(null), size, direction));
      const chains = chainsFrom(absoluteBoxes(first));
      return { chains, laid: await elk.layout(chartGraph(root, lines, chains, size, direction)) };
    };
    Promise.all(directions.map(layout)).then((graphs) => {
      const { chains, laid } = graphs.reduce((best, g) => (fit(g.laid) > fit(best.laid) ? g : best));
      const placed = new Map<string, { x: number; y: number; width?: number; height?: number }>();
      const place = (n: ElkNode) => {
        placed.set(n.id, { x: n.x ?? 0, y: n.y ?? 0, ...(n.children ? { width: n.width, height: n.height } : {}) });
        for (const child of n.children ?? []) place(child);
      };
      for (const child of laid.children ?? []) place(child);
      const laidEdges = new Map((laid.edges ?? []).map((e) => [e.id, e]));
      for (const e of laid.edges ?? [])
        for (const label of e.labels ?? []) if (label.id) placed.set(label.id, { x: label.x ?? 0, y: label.y ?? 0 });
      setNodes((current) =>
        current.map((n) => {
          const at = placed.get(n.id);
          if (at === undefined) return n;
          const { x, y, ...box } = at;
          return { ...n, position: { x, y }, ...box };
        }),
      );
      setEdges(
        lines.map((line) => ({
          id: line.id,
          source: line.source,
          target: line.target,
          type: "transition",
          zIndex: lineZ(root),
          data: {
            points: linePoints(line, chains.get(line.id) as Chain, laidEdges, size),
            transition: line.transition,
          },
        })),
      );
      setLaidOut(true);
    });
  }, [measured, laidOut, nodes, root, width, height, setNodes, setEdges]);
  const shown = useFirstViewport(laidOut, kept, () => fitView({ maxZoom: 1 }));
  return (
    <PickingContext.Provider value={{ picked, pick: onPick }}>
      <ReactFlow
        className={shown ? undefined : "pending"}
        nodes={nodes}
        edges={edges}
        nodeTypes={nodeTypes}
        edgeTypes={edgeTypes}
        onNodesChange={onNodesChange}
        onEdgesChange={onEdgesChange}
        onNodeClick={(_, node) => onPick(node.type !== "state" || node.data.chartKind !== null ? null : node.id)}
        onEdgeClick={(_, edge) => {
          if (edge.data?.transition) onPick(edge.id);
        }}
        onPaneClick={() => onPick(null)}
        onMove={(_, viewport) => onMove(viewport)}
        zIndexMode="manual"
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

export function Chart(props: ChartProps) {
  return (
    <ReactFlowProvider>
      <Diagram {...props} />
    </ReactFlowProvider>
  );
}
