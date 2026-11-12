import { useReactFlow, type Viewport } from "@xyflow/react";
import type { ElkExtendedEdge } from "elkjs/lib/elk-api.js";
import ELK from "elkjs/lib/elk-api.js";
import ElkWorker from "elkjs/lib/elk-worker.min.js?worker";
import { useEffect, useRef, useState } from "react";

export interface Point {
  readonly x: number;
  readonly y: number;
}

/** The layout engine, which runs in a Web Worker so that the page stays responsive. */
export const elk = new ELK({ workerFactory: () => new ElkWorker() });

/**
 * The viewport of a diagram across reloads. `kept` is the viewport before a model reload rebuilt the diagram, or null
 * when another diagram opens.
 */
export interface Keeping {
  readonly kept: Viewport | null;
  readonly onMove: (viewport: Viewport) => void;
}

/** Sets the first viewport after layout and returns false until then, so that the diagram is not shown before it. */
export function useFirstViewport(laidOut: boolean, kept: Viewport | null, fit: () => Promise<unknown>): boolean {
  const [first] = useState(kept);
  const placing = useRef(false);
  const [placed, setPlaced] = useState(false);
  const { setViewport } = useReactFlow();
  useEffect(() => {
    if (!laidOut || placing.current) return;
    placing.current = true;
    requestAnimationFrame(() => (first === null ? fit() : setViewport(first)).then(() => setPlaced(true)));
  }, [laidOut, first, fit, setViewport]);
  return placed;
}

export const cssPx = (name: string) =>
  Number.parseFloat(getComputedStyle(document.documentElement).getPropertyValue(name));

export const edgePoints = (edge: ElkExtendedEdge | undefined): Point[] =>
  (edge?.sections ?? []).flatMap((s) => [s.startPoint, ...(s.bendPoints ?? []), s.endPoint]);

export function roundedPath(points: readonly Point[], corner: number): string {
  const [first, ...rest] = points;
  if (first === undefined) return "";
  const toward = (from: Point, to: Point, length: number): Point => {
    const total = Math.hypot(to.x - from.x, to.y - from.y);
    return total === 0
      ? from
      : { x: from.x + ((to.x - from.x) * length) / total, y: from.y + ((to.y - from.y) * length) / total };
  };
  const parts = [`M ${first.x} ${first.y}`];
  rest.forEach((point, i) => {
    const before = points[i] as Point;
    const after = rest[i + 1];
    if (after === undefined) {
      parts.push(`L ${point.x} ${point.y}`);
      return;
    }
    const r = Math.min(
      corner,
      Math.hypot(point.x - before.x, point.y - before.y) / 2,
      Math.hypot(after.x - point.x, after.y - point.y) / 2,
    );
    const start = toward(point, before, r);
    const end = toward(point, after, r);
    parts.push(`L ${start.x} ${start.y}`, `Q ${point.x} ${point.y} ${end.x} ${end.y}`);
  });
  return parts.join(" ");
}

const arrowId = "arrow";
const openArrowId = "open-arrow";
export const arrowMarker = `url(#${arrowId})`;
export const openArrowMarker = `url(#${openArrowId})`;

export function ArrowDefs() {
  const arrow = cssPx("--size-arrow");
  const marker = (id: string, open: boolean) => (
    <marker
      id={id}
      viewBox={`0 0 ${arrow} ${arrow}`}
      refX={arrow}
      refY={arrow / 2}
      markerWidth={arrow}
      markerHeight={arrow}
      markerUnits="userSpaceOnUse"
      orient="auto-start-reverse"
    >
      <path
        className={open ? "arrowhead open" : "arrowhead"}
        d={`M 0 0 L ${arrow} ${arrow / 2} L 0 ${arrow}${open ? "" : " z"}`}
      />
    </marker>
  );
  return (
    <svg className="defs" aria-hidden="true">
      <defs>
        {marker(arrowId, false)}
        {marker(openArrowId, true)}
      </defs>
    </svg>
  );
}

const crowShapes = ["many", "one", "zeroOrOne"] as const;
type CrowShape = (typeof crowShapes)[number];
const crowId = (shape: CrowShape, picked: boolean) => `crow-${shape}${picked ? "-picked" : ""}`;
export const crowMarker = (shape: CrowShape, picked: boolean) => `url(#${crowId(shape, picked)})`;

export function CrowFootDefs() {
  const size = cssPx("--size-crow");
  const mid = size / 2;
  const bar = (x: number) => `M ${x} 0 L ${x} ${size}`;
  const shapes: Readonly<Record<CrowShape, { readonly path: string; readonly circle: boolean }>> = {
    many: { path: `M 0 ${mid} L ${size} 0 M 0 ${mid} L ${size} ${mid} M 0 ${mid} L ${size} ${size}`, circle: false },
    one: { path: `${bar(size / 2)} ${bar((size * 3) / 4)}`, circle: false },
    zeroOrOne: { path: bar((size * 3) / 4), circle: true },
  };
  return (
    <svg className="defs" aria-hidden="true">
      <defs>
        {[false, true].flatMap((picked) =>
          crowShapes.map((shape) => (
            <marker
              key={crowId(shape, picked)}
              id={crowId(shape, picked)}
              viewBox={`0 0 ${size} ${size}`}
              refX={size}
              refY={mid}
              markerWidth={size}
              markerHeight={size}
              markerUnits="userSpaceOnUse"
              orient="auto-start-reverse"
            >
              <path className={picked ? "crow picked" : "crow"} d={shapes[shape].path} />
              {shapes[shape].circle && (
                <circle className={picked ? "crow picked" : "crow"} cx={size / 4} cy={mid} r={size / 5} />
              )}
            </marker>
          )),
        )}
      </defs>
    </svg>
  );
}
