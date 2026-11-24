//// JSON text for the IR and for finding lines.

import gleam/int
import gleam/list
import gleam/string

pub type Json {
  Str(String)
  Int(Int)
  Bool(Bool)
  Array(List(Json))
  Object(List(#(String, Json)))
}

pub fn encode(j: Json) -> String {
  case j {
    Str(s) -> quote(s)
    Int(n) -> int.to_string(n)
    Bool(True) -> "true"
    Bool(False) -> "false"
    Array(items) -> "[" <> string.join(list.map(items, encode), ",") <> "]"
    Object(fields) ->
      "{"
      <> string.join(
        list.map(fields, fn(f) { quote(f.0) <> ":" <> encode(f.1) }),
        ",",
      )
      <> "}"
  }
}

fn quote(s: String) -> String {
  let body =
    string.to_utf_codepoints(s)
    |> list.map(fn(c) {
      case string.utf_codepoint_to_int(c) {
        0x22 -> "\\\""
        0x5C -> "\\\\"
        0x0A -> "\\n"
        0x0D -> "\\r"
        0x09 -> "\\t"
        n if n < 0x20 -> "\\u" <> string.pad_start(int.to_base16(n), 4, "0")
        _ -> string.from_utf_codepoints([c])
      }
    })
  "\"" <> string.concat(body) <> "\""
}
