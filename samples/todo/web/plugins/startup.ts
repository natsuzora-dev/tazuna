import { definePlugin } from "nitro";
import { fetchService } from "nitro/services";

// Nitro loads the TanStack Start server on the first request, so one request at startup loads it.
export default definePlugin(async () => {
  await fetchService("ssr", "http://localhost/api/ready");
});
