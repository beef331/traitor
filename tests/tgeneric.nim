import balls

import ../traitor
type Generic[X] = distinct tuple[doStuff: proc(_: Atom, val: X): string {.nimcall.}]

implTrait Generic

proc doStuff[H](i: int, val: H): string = $val
proc doStuff[H](i: string, val: H): string = $val
proc doStuff(i: float, val: string): string = $val
proc doStuff(i: float32, val: string) = discard

suite "Generic test":
  test "Compile Time":
    static:
      check "oh".toTrait(Generic[int]).doStuff(200) == $200
      check 100.toTrait(Generic[int]).doStuff(200) == $200
      check "oh".toTrait(Generic[string]).doStuff("what") == "what"
      check 100.toTrait(Generic[string]).doStuff("huzuh") == "huzuh"

  test "Runtime":
    check "oh".toTrait(Generic[int]).doStuff(200) == $200
    check 100.toTrait(Generic[int]).doStuff(200) == $200
    check "oh".toTrait(Generic[string]).doStuff("what") == "what"
    check 100.toTrait(Generic[string]).doStuff("huzuh") == "huzuh"

  test "Ensure checks work":
    check not compiles(10d.toTrait Generic[int])
    check not compiles(10d.toTrait Generic[float])
    check compiles(10d.toTrait Generic[string])
    check not compiles(10f.toTrait Generic[String])
