import ../traitor
import std/macros
import balls


type Generic[X] = distinct tuple[doStuff: proc(_: Atom, val: X): string{.nimcall.}]

implTrait Generic

proc doStuff[H](i: int, val: H): string = $val
proc doStuff[H](i: string, val: H): string = $val

assert "hello".toTrait(Generic[int]).doStuff(100) == $100
assert "hmm".toTrait(Generic[string]).doStuff("bleh") == "bleh"
#assert "oh".toTrait(Generic[int]).doStuff(200) == $200
#assert 100.toTrait(Generic[int]).doStuff(200) == $200


#assert 100.toTrait(Generic[string]).doStuff("what") == "what"
#[
suite "Generic Impls":
  test "doStuff":
    assert 10.toTrait(Generic[int]).doStuff(100) == $100
    assert "oh".toTrait(Generic[string]).doStuff("hmm") == "hmm"

]#
