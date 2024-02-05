import ../traitor
import balls

type RaiseNothing = distinct tuple[doThing: proc(_: Atom){.nimcall, raises: [], noSideEffect.}]
implTrait RaiseNothing

proc doThing(i: int) =
  raise newException(ValueError, "bleh")

proc doThing(i: float) = discard

proc doThing(s: string) = echo s



type RaiseValue = distinct tuple[doStuff: proc(_: Atom){.nimcall, raises: [ValueError].}]

implTrait RaiseValue

proc doStuff(i: float) = raise (ref ValueError)()

proc doStuff(s: string) = raise (ref ValueError)()

proc doStuff(s: bool) = discard

suite "Proc annotations":
  test "raise nothing":
    discard 3d.toTrait RaiseNothing
    check not compiles(10.toTrait RaiseNothing)
    check not compiles("hmm".toTrait RaiseNothing)

  test "raise value":
    expect ValueError, 3d.toTrait(RaiseValue).doStuff()
    expect ValueError, "".toTrait(RaiseValue).doStuff()
    false.toTrait(RaiseValue).doStuff()

