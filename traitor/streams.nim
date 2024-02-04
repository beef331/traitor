## A basic `std/streams` like API built using `Traitor` instead of OOP.

runnableExamples:
  ## Static dispatched API
  var ss = StringStream(data: "Hello")
  assert ss.read(array[5, char]) == "Hello"
  ss.setPos(0)
  assert ss.read(5) == "Hello"
  discard ss.write(", World!")
  ss.setPos(0)
  assert ss.read(array[13, char]) == "Hello, World!"
  ss.setPos(0)
  assert ss.read(array[13, char]) == "Hello, World!"

  var fs = FileStream.init("/tmp/test.txt", fmReadWrite)
  discard fs.write"Hello"
  fs.setPos(0)
  assert fs.read(array[5, char]) == "Hello"
  fs.setPos(0)
  assert fs.read(5) == "Hello"
  discard fs.write(", World!")
  fs.setPos(0)
  assert fs.read(array[13, char]) == "Hello, World!"
  fs.setPos(0)
  assert fs.read(array[13, char]) == "Hello, World!"

  ## Dynamically dispatched API
  var strms = [StringStream().toTrait StreamTrait, FileStream.init("/tmp/test2.txt", fmReadWrite).toTrait StreamTrait]
  for strm in strms.mitems:
    discard strm.write "Hello"
    strm.setPos(0)
    assert strm.read(array[5, char]) == "Hello"
    strm.setPos(0)
    assert strm.read(5) == "Hello"
    discard strm.write(", World!")
    strm.setPos(0)
    assert strm.read(array[13, char]) == "Hello, World!"
    strm.setPos(0)
    assert strm.read(array[13, char]) == "Hello, World!"

import ../traitor
export implTraitProcs
import std/typetraits

type
  StreamTrait* = distinct tuple[
    readData: proc(_: var Atom, dest: pointer, len: int): int {.nimcall.},
    writeData: proc(_: var Atom, toWrite: pointer, len: int): int {.nimcall.},
    setPos: proc(_: var Atom, pos: int) {.nimcall.},
    getPos: proc(_: Atom): int {.nimcall.},
    atEnd: proc(_: Atom): bool {.nimcall.}
  ] ## Any stream must match this trait to be used by this API.
  Stream* = AnyTraitor[StreamTrait] ##
    ## Allows static dispatch where possible, but also dynamic dispatch when converted to a `Traitor[Stream]`

  PrimitiveBase* = concept pb
    pb.distinctBase is PrimitiveAtom
  PrimitiveAtom* = SomeOrdinal or SomeFloat or enum or bool or char or PrimitiveBase or set ##
    ## Built in value types that can be copied by memory

proc onlyPrimitives*(val: typedesc[PrimitiveAtom]): bool =
  ## All PrimitiveAtoms are safe to stream directly.
  true

proc onlyPrimitives*[Idx, T](val: typedesc[array[Idx, T]]): bool =
  ## Procedure to ensure `array`s only are made of prototypes
  onlyPrimitives(T)

proc onlyPrimitives(obj: typedesc[object or tuple]): bool =
  ## Procedure to ensure `object`s only are made of prototypes
  for x in default(obj).fields:
    when not onlyPrimitives(typeof(x)):
      return false
  true

type
  Primitive* = concept type P ## Any type that is `onlyPrimitives(T) is true`
    onlyPrimitives(P)

implTrait StreamTrait

proc read*(strm: var Stream, T: typedesc[Primitive]): T =
  ## Reads the exact amount from `strm`
  ## Raises if it fails to read fully
  mixin readData
  let read = strm.readData(result.addr, sizeof(T))
  if read != sizeof(T):
    raise newException(ValueError, "Did not fully read data, only read: " & $read)

proc read*(strm: var Stream, maxAmount: int): string =
  ## Reads upto `maxAmount` from `strm`
  mixin readData
  result = newString(maxAmount)
  result.setLen(strm.readData(result[0].addr, maxAmount))

proc write*(strm: var Stream, data: Primitive): int =
  ## Writes `data` to `strm`
  mixin writeData
  strm.writeData(data.addr, sizeof(data))

proc write*(strm: var Stream, data: string): int =
  ## Overload for `string` that writes `data`'s data to `strm`
  mixin writeData
  strm.writeData(data[0].addr, data.len)

type
  StringStream* = object
    pos: int
    data*: string

proc atEnd*(ss: StringStream): bool = ss.pos >= ss.data.len

proc readData*(ss: var StringStream, dest: pointer, amount: int): int =
  if amount == 0 or ss.atEnd:
    0
  elif amount <= ss.data.len - ss.pos:
    copyMem(dest, ss.data[ss.pos].addr, amount)
    ss.pos += amount
    amount
  else:
    copyMem(dest, ss.data[ss.pos].addr, ss.data.len - ss.pos)
    ss.pos = ss.data.len
    ss.data.len - ss.pos

proc writeData*(ss: var StringStream, dest: pointer, amount: int): int =
  if amount + ss.pos > ss.data.len:
    ss.data.setLen(amount + ss.pos)
  copyMem(ss.data[ss.pos].addr, dest, amount)
  ss.pos += amount
  amount

proc setPos*(ss: var StringStream, pos: int) = ss.pos = pos
proc getPos*(ss: var StringStream): int = ss.pos

type
  FileStream* = object
    file: File

proc init*(_: typedesc[FileStream], path: string, mode: FileMode = fmRead): FileStream =
  FileStream(file: open(path, mode))

proc `=destroy`(fs: FileStream) =
  close(fs.file)

proc readData*(fs: var FileStream, dest: pointer, amount: int): int =
  fs.file.readBuffer(dest, amount)

proc writeData*(fs: var FileStream, data: pointer, amount: int): int =
  fs.file.writeBuffer(data, amount)

proc atEnd*(fs: var FileStream): bool = fs.file.endOfFile()

proc setPos*(fs: var FileStream, pos: int) = fs.file.setFilePos(pos)
proc getPos*(fs: var FileStream): int = int fs.file.getFilePos()

