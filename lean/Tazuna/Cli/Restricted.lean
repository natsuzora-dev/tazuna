import Tazuna.Linter

/-- Gleam the converter finds outside the subset Lean gives meaning to, by kind. The launcher reports these: Lean never
sees such a spec, so the spec must change. The launcher's copy of this table is generated (`lake exe gen-dsl`). -/
inductive Tazuna.Restricted : Type
  /-- A Float: SMT reals are not IEEE floats, so a spec counts in Int. -/
  | float
  /-- A String literal holding a code point above U+2FFFF: SMT-LIB strings stop there, so tazuna's strings do too. -/
  | highCodePoint
  /-- A bit array, as a value or a pattern. -/
  | bitArray
  /-- `panic`: a spec names its failures as rejections. -/
  | panic
  /-- `todo`, or a function with an empty body: a spec is finished code. -/
  | todo
  /-- `echo`: debugging output is no part of a spec. -/
  | echo
  /-- `let assert`: a spec names its failures, with case and a rejection. -/
  | letAssert
  /-- `assert`: a property is stated as an invariant or an ensures rule. -/
  | assert
  /-- A list spread `[x, ..xs]`: a spec builds lists as literals. -/
  | listSpread
  /-- A list pattern: a spec reads lists through tazuna's functions. -/
  | listPattern
  /-- A string prefix pattern `"a" <> rest`. -/
  | stringPrefixPattern
  /-- An `@external` function: its body is outside Gleam, so it has no meaning to give. -/
  | external
  /-- A function of a module outside the spec's `src/` and tazuna's built-ins, such as the standard library's. -/
  | foreignFunction
  /-- A type of a module outside the spec's `src/` and tazuna's own types. -/
  | foreignType
  /-- A function that calls itself, directly or through others: evaluation must end, and the solver needs it unrolled. -/
  | recursion
  /-- A type that holds itself, directly or through others. -/
  | recursiveType
  /-- `==` or `!=` on a type holding functions, also through a generic function: Gleam compares functions by
  reference, which means nothing in a spec. -/
  | incomparable
  /-- A function the spec keeps (a handler, a rule, an `on_answer`) captures a local that a kept function's values
  cannot hold; the message names the fix. -/
  | keptCapture
  /-- A name defined in a module and also imported unqualified into it: each name means one thing. -/
  | shadowedImport
  /-- A module's value or type referred to both qualified and unqualified in one module: write it one way. -/
  | mixedReference
  /-- A record update on a type with several variants: build the variant with its constructor. -/
  | multiVariantUpdate
  /-- A field access `.label` where the label is no field every variant has at the same place: match the variant with
  case. -/
  | variantField
  /-- A constructor called through a pipe or `use`, or used as a function value: write it applied to every argument. -/
  | constructorValue
  /-- A type the converter cannot infer alone: every parameter, return type, constant and record whose field is read
  carries its annotation. -/
  | annotationNeeded
  /-- The root module defines no `spec() -> tazuna.Spec`, or defines `spec` with another type. -/
  | rootSpec
deriving DecidableEq

namespace Tazuna.Restricted

def all : List Restricted :=
  [float, highCodePoint, bitArray, panic, todo, echo, letAssert, assert, listSpread, listPattern, stringPrefixPattern, external,
    foreignFunction, foreignType, recursion, recursiveType, incomparable, keptCapture, shadowedImport, mixedReference,
    multiVariantUpdate, variantField, constructorValue, annotationNeeded, rootSpec]

theorem mem_all (k : Restricted) : k ∈ all := by cases k <;> simp [all]

def name : Restricted → String
  | float => "float"
  | highCodePoint => "highCodePoint"
  | bitArray => "bitArray"
  | panic => "panic"
  | todo => "todo"
  | echo => "echo"
  | letAssert => "letAssert"
  | assert => "assert"
  | listSpread => "listSpread"
  | listPattern => "listPattern"
  | stringPrefixPattern => "stringPrefixPattern"
  | external => "external"
  | foreignFunction => "foreignFunction"
  | foreignType => "foreignType"
  | recursion => "recursion"
  | recursiveType => "recursiveType"
  | incomparable => "incomparable"
  | keptCapture => "keptCapture"
  | shadowedImport => "shadowedImport"
  | mixedReference => "mixedReference"
  | multiVariantUpdate => "multiVariantUpdate"
  | variantField => "variantField"
  | constructorValue => "constructorValue"
  | annotationNeeded => "annotationNeeded"
  | rootSpec => "rootSpec"

end Tazuna.Restricted
