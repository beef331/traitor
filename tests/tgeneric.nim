import ../traitor
import std/macros
type Generic[X] = distinct tuple[doStuff: proc(_: Atom, val: var X){.nimcall.}]


proc test[X; T: Traitor[Generic]](_: T) = discard

test Traitor[Generic[int]]()

static: assert Generic.isGeneric()

implTrait Generic

proc doStuff[T](i: int, val: T) = echo val

var
  i = 100
  s = "hmm"
10.toTrait(Generic[int]).doStuff(i)
10.toTrait(Generic[string]).doStuff(s)
