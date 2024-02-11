import balls

import ../traitor
type Generic[X] = distinct tuple[doStuff: proc(_: Atom, val: X): string{.nimcall.}]

implTrait Generic

proc doStuff[H](i: int, val: H): string = $val
proc doStuff[H](i: string, val: H): string = $val


static:
  check "oh".toTrait(Generic[int]).doStuff(200) == $200
  check 100.toTrait(Generic[int]).doStuff(200) == $200
  check "oh".toTrait(Generic[string]).doStuff("what") == "what"
  check 100.toTrait(Generic[string]).doStuff("huzuh") == "huzuh"

check "oh".toTrait(Generic[int]).doStuff(200) == $200
check 100.toTrait(Generic[int]).doStuff(200) == $200
check "oh".toTrait(Generic[string]).doStuff("what") == "what"
check 100.toTrait(Generic[string]).doStuff("huzuh") == "huzuh"
