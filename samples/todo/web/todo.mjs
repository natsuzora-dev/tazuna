// The todo service as an implementation, with its own names for tasks and mails. `record` receives every output as a
// line of a tazuna trace.

const hour = 3_600_000;
const rejected = { outcome: "rejected", rejection: { tag: "NoSuchTask" } };

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
      const allowed = name === "remind" ? "Reminder" : "User";
      if (caller.tag !== allowed) return answer(to, { outcome: "invalid", rules: ["callers"] });
      switch (name) {
        case "add": {
          if (input === "") return answer(to, { outcome: "invalid", rules: ["title is not empty"] });
          const task = `task-${++taskCount}`;
          tasks.set(task, { title: input, dueAt: now + hour });
          answer(to, { outcome: "accepted" });
          return event({ tag: "Added", task, title: input });
        }
        case "complete":
          if (!tasks.delete(input)) return answer(to, rejected);
          answer(to, { outcome: "accepted" });
          return event({ tag: "Completed", task: input });
        case "remind":
          if (!tasks.has(input)) return answer(to, rejected);
          answer(to, { outcome: "accepted" });
          return remind(input);
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
