import type { Json } from "@natsuzora-dev/tazuna/view";
import { useState } from "react";

const indent = (depth: number) => "  ".repeat(depth);

function Value({ value, depth }: { readonly value: Json; readonly depth: number }) {
  const [open, setOpen] = useState(depth === 0);
  if (value === null || typeof value !== "object")
    return <span className={typeof value === "string" ? "s" : undefined}>{JSON.stringify(value)}</span>;
  const isArray = Array.isArray(value);
  const entries: readonly (readonly [string | null, Json])[] = isArray
    ? value.map((v) => [null, v] as const)
    : Object.entries(value);
  const [start, end] = isArray ? ["[", "]"] : ["{", "}"];
  if (entries.length === 0) return `${start}${end}`;
  if (!open)
    return (
      <button type="button" className="fold" onClick={() => setOpen(true)}>
        ▸ {start} {entries.length} {isArray ? "items" : "keys"} {end}
      </button>
    );
  return (
    <>
      <button type="button" className="fold" onClick={() => setOpen(false)}>
        ▾ {start}
      </button>
      {entries.map(([key, v], i) => (
        <span key={key ?? i}>
          {`\n${indent(depth + 1)}`}
          {key !== null && <span className="k">{JSON.stringify(key)}</span>}
          {key !== null && ": "}
          <Value value={v} depth={depth + 1} />
          {i < entries.length - 1 && ","}
        </span>
      ))}
      {`\n${indent(depth)}${end}`}
    </>
  );
}

export function JsonView({ value }: { readonly value: Json | object }) {
  return (
    <pre className="json">
      <Value value={value as Json} depth={0} />
    </pre>
  );
}
