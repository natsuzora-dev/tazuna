import type { DefinitionView, EntityView, FieldView, ServiceView } from "@natsuzora-dev/tazuna/view";
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
} from "@xyflow/react";
import type { ElkNode } from "elkjs/lib/elk-api.js";
import { createContext, type MouseEvent, useContext, useEffect, useState } from "react";
import {
  CrowFootDefs,
  crowMarker,
  cssPx,
  edgePoints,
  elk,
  type Keeping,
  type Point,
  roundedPath,
  useFirstViewport,
} from "./diagram.tsx";

interface PlacedEntity {
  readonly service: string;
  readonly definition: DefinitionView;
  readonly entity: EntityView;
}

type KeyedEntity = PlacedEntity & { readonly entity: { readonly key: string } };

export type ErPick =
  | { readonly type: "entity"; readonly placed: PlacedEntity }
  | { readonly type: "field" | "ref"; readonly placed: PlacedEntity; readonly field: FieldView };

const entityId = (service: string, name: string) => `entity:${service}/${name}`;
const rowId = (placed: PlacedEntity, field: string) => `${entityId(placed.service, placed.definition.name)}/${field}`;
const refId = (from: PlacedEntity, field: string) => `ref:${rowId(from, field)}`;
const portId = (row: string, side: "WEST" | "EAST") => `${row}:${side}`;

interface Picking {
  readonly highlighted: readonly string[];
  readonly pick: (id: string | null) => void;
}
const PickingContext = createContext<Picking>({ highlighted: [], pick: () => {} });

const entityName = (service: string, name: string, shownFrom: string) =>
  service === shownFrom ? name : `${service}.${name}`;

function FieldRow({ placed, field, shownFrom }: { placed: PlacedEntity; field: FieldView; shownFrom: string }) {
  const { highlighted, pick } = useContext(PickingContext);
  const id = rowId(placed, field.name);
  const onClick = (e: MouseEvent) => {
    e.stopPropagation();
    pick(id);
  };
  return (
    <li>
      <button
        type="button"
        className={field.ref === null ? "field" : "field ref"}
        data-field={field.name}
        aria-pressed={highlighted.includes(id)}
        onClick={onClick}
      >
        <span>
          {field.name}
          {field.name === placed.entity.key && <span className="key"> key</span>}
        </span>
        <span className="type">
          {field.ref === null ? field.type : `→ ${entityName(field.ref.service, field.ref.name, shownFrom)}`}
          {field.nullable && "?"}
          {placed.entity.unique.includes(field.name) && " · unique"}
        </span>
      </button>
    </li>
  );
}

type EntityNode = Node<{ readonly placed: PlacedEntity; readonly shownFrom: string }, "entity">;
type RefEdge = Edge<{ readonly points: readonly Point[]; readonly field: FieldView }, "ref">;

function EntityBox({ id, data: { placed, shownFrom } }: NodeProps<EntityNode>) {
  const { highlighted } = useContext(PickingContext);
  const { definition, entity } = placed;
  return (
    <div className={highlighted.includes(id) ? "entity box picked" : "entity box"}>
      <Handle type="target" position={Position.Left} isConnectable={false} />
      <div className="entity-head">
        <span className="kind">{entity.key === null ? "single entity" : "entity"}</span>
        <span className="name">{entityName(placed.service, definition.name, shownFrom)}</span>
        <span className="desc">{(definition.definition as { readonly description: string }).description}</span>
      </div>
      <ul>
        {entity.fields.map((field) => (
          <FieldRow key={field.name} placed={placed} field={field} shownFrom={shownFrom} />
        ))}
      </ul>
      <Handle type="source" position={Position.Right} isConnectable={false} />
    </div>
  );
}

function RefLine({ id, data }: EdgeProps<RefEdge>) {
  const { highlighted } = useContext(PickingContext);
  const picked = highlighted.includes(id);
  return (
    <BaseEdge
      id={id}
      className={picked ? "picked" : undefined}
      path={roundedPath(data?.points ?? [], cssPx("--radius-corner"))}
      markerStart={crowMarker("many", picked)}
      markerEnd={crowMarker(data?.field.nullable ? "zeroOrOne" : "one", picked)}
      interactionWidth={cssPx("--space-part")}
    />
  );
}

const nodeTypes = { entity: EntityBox };
const edgeTypes = { ref: RefLine };

interface Ref {
  readonly id: string;
  readonly from: PlacedEntity;
  readonly field: FieldView;
  readonly to: KeyedEntity;
}

function erParts(services: readonly ServiceView[], shown: string): { placed: PlacedEntity[]; refs: Ref[] } {
  const all = services.flatMap((service) =>
    service.definitions.flatMap((definition) =>
      definition.entity === null ? [] : [{ service: service.name, definition, entity: definition.entity }],
    ),
  );
  const keyed = all.filter((p): p is KeyedEntity => p.entity.key !== null);
  const find = (service: string, name: string) =>
    keyed.find((p) => p.service === service && p.definition.name === name) as KeyedEntity;
  const own = all.filter((p) => p.service === shown);
  const refs = own.flatMap((from) =>
    from.entity.fields.flatMap((field) =>
      field.ref === null
        ? []
        : [{ id: refId(from, field.name), from, field, to: find(field.ref.service, field.ref.name) }],
    ),
  );
  const others = [...new Set(refs.map((r) => r.to).filter((p) => p.service !== shown))];
  return { placed: [...own, ...others], refs };
}

export function erPick(services: readonly ServiceView[], shown: string, id: string): ErPick | undefined {
  for (const placed of erParts(services, shown).placed) {
    if (entityId(placed.service, placed.definition.name) === id) return { type: "entity", placed };
    for (const field of placed.entity.fields) {
      if (rowId(placed, field.name) === id) return { type: "field", placed, field };
      if (field.ref !== null && refId(placed, field.name) === id) return { type: "ref", placed, field };
    }
  }
  return undefined;
}

function erGraph(placed: readonly PlacedEntity[], refs: readonly Ref[], nodes: readonly EntityNode[]): ElkNode {
  const ends = refs.flatMap((r) => [
    { placed: r.from, field: r.field.name, side: "EAST" as const },
    { placed: r.to, field: r.to.entity.key, side: "WEST" as const },
  ]);
  return {
    id: "er",
    layoutOptions: {
      "elk.algorithm": "layered",
      "elk.direction": "RIGHT",
      "elk.edgeRouting": "ORTHOGONAL",
      "elk.layered.nodePlacement.strategy": "NETWORK_SIMPLEX",
      "elk.spacing.nodeNode": String(cssPx("--space-node-gap")),
      "elk.layered.spacing.nodeNodeBetweenLayers": String(cssPx("--space-layer-gap")),
      "elk.spacing.edgeNode": String(cssPx("--space-row")),
      "elk.spacing.edgeEdge": String(cssPx("--space-part")),
    },
    children: placed.map((p) => {
      const id = entityId(p.service, p.definition.name);
      const { width = 0, height = 0 } = nodes.find((n) => n.id === id)?.measured ?? {};
      const box = document.querySelector(`.react-flow__node[data-id="${CSS.escape(id)}"]`);
      const center = (field: string) => {
        const row = box?.querySelector<HTMLElement>(`[data-field="${CSS.escape(field)}"]`);
        return row ? row.offsetTop + row.offsetHeight / 2 : 0;
      };
      const ports = new Map(
        ends
          .filter((e) => e.placed === p)
          .map((e) => [
            portId(rowId(p, e.field), e.side),
            { x: e.side === "EAST" ? width : 0, y: center(e.field), side: e.side },
          ]),
      );
      return {
        id,
        width,
        height,
        layoutOptions: { "elk.portConstraints": "FIXED_POS" },
        ports: [...ports].map(([port, { x, y, side }]) => ({
          id: port,
          x,
          y,
          width: 0,
          height: 0,
          layoutOptions: { "elk.port.side": side },
        })),
      };
    }),
    edges: refs.map((r) => ({
      id: r.id,
      sources: [portId(rowId(r.from, r.field.name), "EAST")],
      targets: [portId(rowId(r.to, r.to.entity.key), "WEST")],
    })),
  };
}

interface ErProps extends Keeping {
  readonly services: readonly ServiceView[];
  readonly service: string;
  readonly picked: string | null;
  readonly onPick: (id: string | null) => void;
}

function Diagram({ services, service, picked, onPick, kept, onMove }: ErProps) {
  const [{ placed, refs }] = useState(() => erParts(services, service));
  const [nodes, setNodes, onNodesChange] = useNodesState<EntityNode>(
    placed.map((p) => ({
      id: entityId(p.service, p.definition.name),
      type: "entity",
      position: { x: 0, y: 0 },
      data: { placed: p, shownFrom: service },
    })),
  );
  const [edges, setEdges] = useState<RefEdge[]>([]);
  const [laidOut, setLaidOut] = useState(false);
  const measured = useNodesInitialized();
  const { fitView } = useReactFlow();
  useEffect(() => {
    if (!measured || laidOut) return;
    elk.layout(erGraph(placed, refs, nodes)).then((laid) => {
      const at = new Map((laid.children ?? []).map((n) => [n.id, { x: n.x ?? 0, y: n.y ?? 0 }]));
      const laidEdges = new Map((laid.edges ?? []).map((e) => [e.id, e]));
      setNodes((current) => current.map((n) => ({ ...n, position: at.get(n.id) ?? n.position })));
      setEdges(
        refs.map((r) => ({
          id: r.id,
          source: entityId(r.from.service, r.from.definition.name),
          target: entityId(r.to.service, r.to.definition.name),
          type: "ref",
          data: { points: edgePoints(laidEdges.get(r.id)), field: r.field },
        })),
      );
      setLaidOut(true);
    });
  }, [measured, laidOut, nodes, placed, refs, setNodes]);
  const shown = useFirstViewport(laidOut, kept, () => fitView({ maxZoom: 1 }));
  const ref = refs.find((r) => r.id === picked);
  const highlighted =
    ref !== undefined
      ? [ref.id, rowId(ref.from, ref.field.name), rowId(ref.to, ref.to.entity.key)]
      : picked === null
        ? []
        : [picked];
  return (
    <PickingContext.Provider value={{ highlighted, pick: onPick }}>
      <ReactFlow
        className={shown ? undefined : "pending"}
        nodes={nodes}
        edges={edges}
        nodeTypes={nodeTypes}
        edgeTypes={edgeTypes}
        onNodesChange={onNodesChange}
        onNodeClick={(_, node) => onPick(node.id)}
        onEdgeClick={(_, edge) => onPick(edge.id)}
        onPaneClick={() => onPick(null)}
        onMove={(_, viewport) => onMove(viewport)}
        nodesDraggable={false}
        nodesConnectable={false}
        elementsSelectable={false}
        edgesFocusable={false}
      >
        <CrowFootDefs />
        <Background gap={cssPx("--space-edge")} size={cssPx("--size-dot") * 2} />
        <Controls showInteractive={false} />
      </ReactFlow>
    </PickingContext.Provider>
  );
}

export function Er(props: ErProps) {
  return (
    <ReactFlowProvider>
      <Diagram {...props} />
    </ReactFlowProvider>
  );
}
