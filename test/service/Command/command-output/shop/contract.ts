import { cancelOrder, contract, placeOrder } from "./shop.ts";

export const shop = contract({ placeOrder, cancelOrder });
