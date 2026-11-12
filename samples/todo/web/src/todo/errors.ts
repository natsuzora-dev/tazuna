export const commandErrors = {
  TASK_ALREADY_EXISTS: { status: 409 },
  TASK_NOT_FOUND: { status: 404 },
  ALREADY_COMPLETED: { status: 409 },
  NOT_COMPLETED: { status: 409 },
  DUE_IN_PAST: { status: 422 },
  IDEMPOTENCY_KEY_REUSED: { status: 422 },
};
