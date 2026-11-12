import { createRootRoute, HeadContent, Scripts } from "@tanstack/react-router";
import type { ReactNode } from "react";
import { NotificationDevice } from "../device/NotificationDevice.tsx";
import styles from "../styles.css?url";

export const Route = createRootRoute({
  head: () => ({
    meta: [
      { charSet: "utf-8" },
      { name: "viewport", content: "width=device-width, initial-scale=1" },
      { title: "Tasks" },
    ],
    links: [{ rel: "stylesheet", href: styles }],
  }),
  shellComponent: RootDocument,
});

function RootDocument({ children }: { children: ReactNode }) {
  return (
    <html lang="en">
      <head>
        <HeadContent />
      </head>
      <body>
        <main>
          <NotificationDevice />
          {children}
        </main>
        <Scripts />
      </body>
    </html>
  );
}
