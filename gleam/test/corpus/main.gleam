//// Converter corpus: every construct the converter maps, written for it.

import corpus/shapes.{type Count, type Shape, Circle, Rect}
import gleam/option.{type Option, None, Some}
import tazuna
import tazuna/bag
import tazuna/table

pub type Event {
  Opened(id: Int, title: String)
  Closed(id: Int)
}

pub const limits: #(Int, Int) = #(1000, -0x_F)

pub const names: List(String) = ["a\tb", "tab	raw", "\u{1F600}\"\\"]

pub const pick: fn(Int, String) -> Int = choose

pub const both = #(limits, step)

pub const step = shapes.unit

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [], externals: [])
}

pub fn choose(first a: Int, second _b: String) -> Int {
  a
}

pub fn labels() -> Int {
  let x = choose(second: "s", first: 1)
  let second = "t"
  let y = choose(2, second:)
  x + y
}

pub fn pipes(n: Int) -> Int {
  let a = n |> choose(second: "x")
  let b = "y" |> choose(first: a)
  let c = n |> fn(k) { k * 2 }
  let adder = fn(k: Int) -> fn(Int) -> Int { fn(j) { k + j } }
  let d = n |> adder(1)()
  a + b + c + d
}

pub fn with_callback(
  k: Int,
  then f: fn(Int, String) -> Result(Int, String),
) -> Result(Int, String) {
  f(k, "v")
}

pub fn with_unit(f: fn(Nil) -> Int) -> Int {
  f(Nil)
}

pub fn uses() -> Result(Int, String) {
  use n: Count, _s <- with_callback(3)
  Ok(n + units())
}

pub fn units() -> Int {
  use _ <- with_unit
  1
}

pub fn lets(e: Event) -> Int {
  let #(a, b): #(Int, _) = #(1, "two")
  let shapes.Pair(c, _) = shapes.Pair(3, b)
  let id = e.id
  { a + c } * id
}

pub fn cases(e: Event, n: Int, s: String) -> String {
  case e, n {
    Opened(title:, ..), _ if title != "" -> title <> s
    Opened(id: 10, ..), _ | Closed(id: 10), _ -> "ten"
    Closed(..) as closed, -2 -> describe(closed)
    _, 0x1F -> "hex"
    _, _ ->
      case s {
        "\t" -> "tab"
        _ -> "other"
      }
  }
}

pub fn describe(e: Event) -> String {
  case e {
    Opened(_, title) -> title
    Closed(_) -> "closed"
  }
}

pub fn options(o: Option(Int)) -> Option(Int) {
  case o {
    Some(x) if x > 0 -> Some(x - 1)
    Some(_) -> None
    None -> None
  }
}

pub fn shapes_use(s: Shape) -> #(Int, String, Int) {
  let c = Circle(name: "c", r: 2)
  let r = Rect("r", 1, h: 3)
  let total = shapes.area(of: c) + shapes.area(r) + shapes.area(s)
  #(total, shapes.label(s), shapes.unit)
}

pub fn generics() -> Int {
  let box = shapes.Box(item: 1, count: 0)
  let named = shapes.map_box(box, with: fn(i) { "item" <> describe(Closed(i)) })
  let bumped = shapes.bump(named)
  bumped.count
}

pub fn operators(a: Int, b: Int, p: Bool) -> Bool {
  let n = a + b - a * b / 2 % 3
  let m = -n
  let q = !p
  n < m && m <= a || a > b && b >= n && q == p && a != b
}

pub fn lists() -> List(List(Int)) {
  let empty = []
  [[1, 2], empty, [limits.0]]
}

pub fn bodies() -> fn() -> Int {
  fn() { { 1 } }
}

pub fn aliases(n: Count) -> shapes.Counts {
  let pair: shapes.Twice(Count) = #(n, shapes.tally(of: #(n, 1)).total)
  pair
}

pub fn trailing(n: Count) -> #(Int, Count) {
  let #(_a, _): shapes.Counts = #(n, n)
}

pub fn statements(f: fn() -> Int) -> Int {
  f()
  let g = fn() -> Int {
    let x = f()
    x
  }
  g() + pick(1, "p")
}

pub type Rejection {
  Missing
  TooLong
}

pub fn builtins(
  titles: table.Table(Int, String),
  id: Int,
  at: tazuna.Instant,
) -> Result(#(Int, tazuna.Instant), Rejection) {
  use title <- table.lookup(titles, id, or: Missing)
  use <- tazuna.require(tazuna.length(title) <= 10, or: TooLong)
  let lengths =
    table.values(titles)
    |> bag.map(with: tazuna.length)
  let longest = case bag.max_by(lengths, by: fn(n) { n }) {
    Ok(n) -> n
    Error(bag.Empty) -> 0
    Error(bag.Tie) -> -1
  }
  Ok(#(longest, at))
}

pub fn captures(ids: bag.Bag(Int)) -> #(bag.Bag(Event), Int, Option(Event)) {
  let closed = bag.map(ids, with: Closed)
  let opened = bag.map(ids, with: Opened(_, "new"))
  let titled = bag.map(ids, with: Opened(title: "t", id: _))
  let firsts = choose(second: "s", first: _)
  let wrap = Some
  #(closed, bag.size(opened) + bag.size(titled) + firsts(1), wrap(Closed(2)))
}

pub fn rules(n: Int, wait: tazuna.Duration) -> tazuna.Rules {
  [#("positive", n > 0), #("waits", wait >= 0)]
}
