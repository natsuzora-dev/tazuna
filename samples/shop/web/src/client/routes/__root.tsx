import { type QueryClient, useMutation, useQuery, useQueryClient } from "@tanstack/react-query";
import { createRootRouteWithContext, Link, Outlet } from "@tanstack/react-router";
import { body, sessionApi } from "../api.ts";

export const Route = createRootRouteWithContext<{ queryClient: QueryClient }>()({ component: Root });

function Root() {
  const queryClient = useQueryClient();
  const session = useQuery({ queryKey: ["session"], queryFn: () => sessionApi.index.$get().then(body) });
  const signIn = useMutation({
    mutationFn: (role: "customer" | "staff") => sessionApi.index.$put({ json: { role } }).then(body),
    onSuccess: () => queryClient.invalidateQueries(),
  });
  const role = session.data?.role;

  return (
    <>
      <header>
        <nav>
          <Link to="/">Shop</Link>
          <Link to="/staff">Staff</Link>
        </nav>
        <div className="session">
          <span>{role ? `Signed in as ${role}` : "Not signed in"}</span>
          <button type="button" onClick={() => signIn.mutate("customer")} disabled={role === "customer"}>
            Sign in as customer
          </button>
          <button type="button" onClick={() => signIn.mutate("staff")} disabled={role === "staff"}>
            Sign in as staff
          </button>
        </div>
      </header>
      <main>
        <Outlet />
      </main>
    </>
  );
}
