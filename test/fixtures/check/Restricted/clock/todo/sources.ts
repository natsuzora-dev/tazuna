// Property names and keys named like globals do not read the globals.
export const labels = { Date: "date", crypto: "crypto", process: "process" };

export const dateOf = (row: { readonly Date: string }) => row.Date;
