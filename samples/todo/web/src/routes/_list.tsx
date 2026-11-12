import { useQuery } from "@tanstack/react-query";
import { createFileRoute, Outlet, retainSearchParams } from "@tanstack/react-router";
import { todo } from "@todo/spec/todo";
import { z } from "zod";
import { orpc } from "../orpc/client.ts";

export const Route = createFileRoute("/_list")({
  validateSearch: z.object({ filter: todo.tasks.input.filter.optional() }),
  search: { middlewares: [retainSearchParams(["filter"])] },
  component: ListSubscriptions,
});

function ListSubscriptions() {
  const { filter = "open" } = Route.useSearch();
  useQuery(orpc.todo.tasks.experimental_liveOptions({ input: { filter } }));
  useQuery(orpc.todo.reminderSettings.experimental_liveOptions({ input: {} }));
  return <Outlet />;
}
