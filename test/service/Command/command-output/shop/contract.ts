import { contract } from "@natsuzora-dev/tazuna";
import { cancelOrder, placeOrder } from "./shop.ts";

export const shop = contract({ placeOrder, cancelOrder });
