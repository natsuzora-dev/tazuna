import { definitionKinds, type ServiceView } from "@natsuzora-dev/tazuna/view";
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
} from "@xyflow/react";
import type { ElkNode } from "elkjs/lib/elk-api.js";
import { useEffect, useState } from "react";
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

type ServiceNode = Node<{ readonly service: ServiceView }, "service">;
type UsesEdge = Edge<{ readonly points: readonly Point[] }, "uses">;

function ServiceBox({ data: { service } }: NodeProps<ServiceNode>) {
  const counts = definitionKinds
    .map((kind) => [kind, service.definitions.filter((d) => d.kind === kind).length] as const)
    .filter(([, count]) => count > 0);
  return (
    <div className="node box">
      <Handle type="target" position={Position.Left} isConnectable={false} />
      <div className="kind">{service.kind}</div>
      <div className="name">{service.name}</div>
      <div className="desc">{service.description}</div>
      {counts.length > 0 && (
        <div className="counts">
          {counts.map(([kind, count]) => (
            <span key={kind} className={`chip c-${kind}`}>
              {count} {kind}
            </span>
          ))}
        </div>
      )}
      <Handle type="source" position={Position.Right} isConnectable={false} />
    </div>
  );
}

function UsesLine({ id, data }: EdgeProps<UsesEdge>) {
  return <BaseEdge id={id} path={roundedPath(data?.points ?? [], cssPx("--radius-corner"))} markerEnd={arrowMarker} />;
}

const nodeTypes = { service: ServiceBox };
const edgeTypes = { uses: UsesLine };

interface ServiceMapProps extends Keeping {
  readonly services: readonly ServiceView[];
  readonly picked: string | null;
  readonly onPick: (name: string | null) => void;
}

function Diagram({ services, picked, onPick, kept, onMove }: ServiceMapProps) {
  const [nodes, setNodes, onNodesChange] = useNodesState<ServiceNode>(
    services.map((service) => ({
      id: service.name,
      type: "service",
      position: { x: 0, y: 0 },
      selected: service.name === picked,
      data: { service },
    })),
  );
  const [edges, setEdges, onEdgesChange] = useEdgesState<UsesEdge>([]);
  const [laidOut, setLaidOut] = useState(false);
  const measured = useNodesInitialized();
  const { fitView } = useReactFlow();
  useEffect(() => {
    if (!measured || laidOut) return;
    const uses = services.flatMap((s) =>
      s.uses.map((used) => ({ id: `${s.name}>${used}`, source: s.name, target: used })),
    );
    const graph: ElkNode = {
      id: "root",
      layoutOptions: {
        "elk.algorithm": "layered",
        "elk.direction": "RIGHT",
        "elk.edgeRouting": "ORTHOGONAL",
        "elk.spacing.nodeNode": String(cssPx("--space-node-gap")),
        "elk.layered.spacing.nodeNodeBetweenLayers": String(cssPx("--space-layer-gap")),
      },
      children: nodes.map((n) => ({ id: n.id, width: n.measured?.width ?? 0, height: n.measured?.height ?? 0 })),
      edges: uses.map((e) => ({ id: e.id, sources: [e.source], targets: [e.target] })),
    };
    elk.layout(graph).then((laid) => {
      const placed = new Map(laid.children?.map((c) => [c.id, { x: c.x ?? 0, y: c.y ?? 0 }]));
      setNodes((current) => current.map((n) => ({ ...n, position: placed.get(n.id) ?? n.position })));
      setEdges(
        uses.map((e) => ({ ...e, type: "uses", data: { points: edgePoints(laid.edges?.find((g) => g.id === e.id)) } })),
      );
      setLaidOut(true);
    });
  }, [measured, laidOut, nodes, services, setNodes, setEdges]);
  const shown = useFirstViewport(laidOut, kept, () => fitView({ maxZoom: 1 }));
  return (
    <ReactFlow
      className={shown ? undefined : "pending"}
      nodes={nodes}
      edges={edges}
      nodeTypes={nodeTypes}
      edgeTypes={edgeTypes}
      onNodesChange={onNodesChange}
      onEdgesChange={onEdgesChange}
      onSelectionChange={({ nodes: chosen }) => onPick(chosen[0]?.id ?? null)}
      onMove={(_, viewport) => onMove(viewport)}
      nodesDraggable={false}
      nodesConnectable={false}
      edgesFocusable={false}
      multiSelectionKeyCode={null}
      selectionKeyCode={null}
    >
      <ArrowDefs />
      <Background gap={cssPx("--space-edge")} size={cssPx("--size-dot") * 2} />
      <Controls showInteractive={false} />
    </ReactFlow>
  );
}

export function ServiceMap(props: ServiceMapProps) {
  return (
    <ReactFlowProvider>
      <Diagram {...props} />
    </ReactFlowProvider>
  );
}
