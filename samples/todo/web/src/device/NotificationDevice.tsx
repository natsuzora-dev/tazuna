import { useEffect, useState } from "react";
import { client } from "../orpc/client.ts";
import { useEvents } from "../orpc/useEvents.ts";

const subscribeDeviceRequests = () =>
  client.device.deviceRequests(undefined, { context: { retry: Number.POSITIVE_INFINITY } });

const report = (permission: "granted" | "denied") =>
  client.device.reportNotificationPermission({ granted: permission === "granted" });

export function NotificationDevice() {
  const [isSupported, setIsSupported] = useState(false);
  useEffect(() => setIsSupported("Notification" in window), []);
  return isSupported ? <Device /> : null;
}

function Device() {
  const [isAsking, setIsAsking] = useState(false);

  useEvents(subscribeDeviceRequests, async (request) => {
    if (request.name === "showNotification") {
      const isShown = Notification.permission === "granted";
      if (isShown) new Notification(request.input.text);
      await client.device.answerDeviceRequest({ id: request.id, accepted: isShown });
      return;
    }
    await client.device.answerDeviceRequest({ id: request.id, accepted: true });
    // Browsers show the permission dialog only during a user gesture, so a button asks.
    if (Notification.permission === "default") setIsAsking(true);
    else await report(Notification.permission);
  });

  // The user can also grant or revoke in the browser settings. The spec has no event for a return to prompt.
  useEffect(() => {
    let status: PermissionStatus | undefined;
    void navigator.permissions.query({ name: "notifications" }).then((s) => {
      status = s;
      s.onchange = () => {
        if (s.state !== "prompt") void report(s.state);
      };
    });
    return () => {
      if (status !== undefined) status.onchange = null;
    };
  }, []);

  if (!isAsking) return null;
  return (
    <div className="permission">
      <span>Allow notifications in your browser to get reminders</span>
      <button
        type="button"
        className="link"
        onClick={async () => {
          setIsAsking(false);
          const permission = await Notification.requestPermission();
          // Closing the prompt leaves default: neither granted nor denied.
          if (permission === "default") setIsAsking(true);
          else await report(permission);
        }}
      >
        Allow
      </button>
    </div>
  );
}
