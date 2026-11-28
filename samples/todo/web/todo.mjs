// The todo service as an implementation, with its own names for tasks and mails. `record` receives every output as a
// line of a tazuna trace.

const hour = 3_600_000;
const rejected = (tag) => ({ outcome: "rejected", rejection: { tag } });
const maxOpen = 2;
// The requests outside callers may send. Reminders run only from the clock.
const publicRequests = new Set(["add", "complete", "open tasks"]);

export function createTodo(record) {
  const tasks = new Map();
  let now = 0;
  let taskCount = 0;
  let mailCount = 0;

  const out = (line) => record({ ...line, time: now });
  const answer = (to, outcome) => out({ out: "answer", to, ...outcome });
  const event = (value) => out({ out: "event", value });

  const remind = (task) => {
    const { title } = tasks.get(task);
    event({ tag: "ReminderDue", task, title });
    out({
      out: "request",
      external: "mailer",
      name: "send",
      id: `mail-${++mailCount}`,
      input: { tag: "Mail", subject: title },
    });
  };

  return {
    request({ id: to, name, caller, input, time }) {
      now = time;
      if (!publicRequests.has(name) || caller.tag !== "User") {
        return answer(to, { outcome: "invalid", rules: ["callers"] });
      }
      switch (name) {
        case "add": {
          if (input === "") return answer(to, { outcome: "invalid", rules: ["title is not empty"] });
          if (tasks.size >= maxOpen) return answer(to, rejected("TooManyOpenTasks"));
          const task = `task-${++taskCount}`;
          tasks.set(task, { title: input, dueAt: now + hour });
          answer(to, { outcome: "accepted" });
          return event({ tag: "Added", task, title: input });
        }
        case "complete":
          if (!tasks.delete(input)) return answer(to, rejected("NoSuchTask"));
          answer(to, { outcome: "accepted" });
          return event({ tag: "Completed", task: input });
        case "open tasks":
          return answer(to, { outcome: "answered", output: tasks.size });
      }
    },

    clock(time) {
      now = time;
      for (const [task, state] of tasks) {
        if (state.dueAt !== undefined && state.dueAt <= now) {
          state.dueAt = undefined;
          remind(task);
        }
      }
    },

    // The spec writes no event for the mailer's answer.
    answer() {},
  };
}
