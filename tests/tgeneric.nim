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



type Observer*[T] = ref object
  subscription: proc(value: T)
  error: proc(error: CatchableError)
  complete: proc()

type Observable*[T] = ref object
  observers: seq[Observer[T]]
  values: seq[T]
  complete: bool

type Subject*[T] = ref object
  observers: seq[Observer[T]]
  complete: bool

type Reactable[T] = distinct tuple [
  getObservers: proc(a: Atom): seq[Observer[T]] {.nimcall.}
]

implTrait Reactable
proc getObservers[T](reactable: Observable[T]): seq[Observer[T]] = reactable.observers
proc getObservers[T](reactable: Subject[T]): seq[Observer[T]] = reactable.observers

var subject = Subject[int]().toTrait(Reactable[int])


type
  Trait = distinct tuple[
    sendMessage: proc(self: Atom, message: openArray[char]): string
  ]
  Sender = object

implTrait Trait

proc sendMessage(self: Sender, message: openArray[char]): string = $message

check Sender().toTrait(Trait).sendMessage("Hello, world!") == "['H', 'e', 'l', 'l', 'o', ',', ' ', 'w', 'o', 'r', 'l', 'd', '!']"

import pkg/traitor
type
  GenericTrait[T] = distinct tuple[
    initialize: proc(self: Atom, userdata: T),
  ]
  FileSender[T] = object
  Message = object
    bytes: array[16, char]

implTrait GenericTrait

proc initialize(self: FileSender[Message], userdata: Message) = check userData == default(Message)

FileSender[Message]().toTrait(GenericTrait[Message]).initialize(Message())
