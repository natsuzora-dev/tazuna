import { at, elsewhere, from, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { board, watchingBoard } from "../board/contract.ts";
import { addNote, addTask, noteList } from "./notes.ts";

const start = at("2026-10-25T09:00:00+09:00");

const watchedByBoard = subscribe(noteList, {});

export const endsBoardSubscriptionPlainly = scenario(
  "Take the subscription of board to the notes, then end it as from no service; only board ends its subscription, so check reports namedInputUnplaced",
  [start, from(board, watchedByBoard), unsubscribe(watchedByBoard)],
);

const watched = subscribe(noteList, {});

export const endsSubscriptionFromBoard = scenario(
  "Subscribe to the notes, then end the subscription as from board; board did not open it, so check reports namedInputUnplaced",
  [start, watched, from(board, unsubscribe(watched))],
);

export const endsUnopenedBoardSubscription = scenario(
  "End, in board's run, a subscription to board that no line of that run opens; check reports namedInputUnplaced",
  [start, elsewhere(board, unsubscribe(watchingBoard))],
);

export const endsGivenBoardSubscription = scenario(
  "End, in board's run, the subscription that board's given state opens; the state and the elsewhere inputs form one run, so check reports nothing",
  [start, elsewhere(board, unsubscribe(watchingBoard))],
  { given: { board: board.states.watched } },
);

export const namesNoteTwice = scenario("Name two notes N-milk on one task; check reports keyNamedTwice", [
  start,
  send(addTask, { taskId: "task-1" }, { keys: { Note: ["N-milk", "N-milk"] } }),
]);

export const namesNoteAgain = scenario(
  "Name the note of the second task N-milk as the first's; check reports keyNamedTwice",
  [
    start,
    send(addTask, { taskId: "task-1" }, { keys: { Note: ["N-milk"] } }),
    send(addTask, { taskId: "task-2" }, { keys: { Note: ["N-milk"] } }),
  ],
);

export const usesNameBeforeNaming = scenario(
  "Add the note N-milk, then name N-milk the note of a task; the first line uses the name before the line that names it, so check reports keyUsedBeforeNamed",
  [
    start,
    send(addNote, { noteId: "N-milk", label: "milk" }),
    send(addTask, { taskId: "task-1" }, { keys: { Note: ["N-milk"] } }),
  ],
);

export const namesCountedNote = scenario(
  "Name the note of a task Note-1, the form of a counted key; check reports countedKey",
  [start, send(addTask, { taskId: "task-1" }, { keys: { Note: ["Note-1"] } })],
);

export const usesTagForm = scenario(
  "Add a note labelled Tag-1, the form of a counted key of tags, a service that the scenario does not involve; check reports nothing",
  [start, send(addNote, { noteId: "N-tag", label: "Tag-1" })],
);
