import { deviceRouter } from "../device/device.router.ts";
import { todoRouter } from "../todo/todo.router.ts";

export const router = { todo: todoRouter, device: deviceRouter };
