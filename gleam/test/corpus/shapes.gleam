//// Converter corpus: types and helpers another module imports.

pub type Shape {
  Circle(name: String, r: Int)
  Rect(name: String, w: Int, h: Int)
}

pub type Box(a) {
  Box(item: a, count: Int)
}

pub type Pair {
  Pair(Int, String)
}

pub type Twice(a) =
  #(a, a)

pub type Counts =
  Twice(Count)

pub type Count =
  Int

pub type Tally {
  Tally(counts: Counts, total: Count)
}

pub const unit: Int = 1

pub fn area(of shape: Shape) -> Int {
  case shape {
    Circle(r:, ..) -> 3 * r * r
    Rect(w: width, h: height, name: _) -> width * height
  }
}

pub fn label(shape: Shape) -> String {
  shape.name
}

pub fn map_box(box: Box(a), with f: fn(a) -> b) -> Box(b) {
  Box(item: f(box.item), count: box.count)
}

pub fn tally(of counts: Counts) -> Tally {
  Tally(counts:, total: counts.0 + counts.1)
}

pub fn bump(box: Box(a)) -> Box(a) {
  Box(..box, count: box.count + unit)
}
