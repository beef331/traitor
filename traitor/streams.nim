import ../traitor
import std/typetraits

type
  StreamTrait* = distinct tuple[
    readData: proc(_: var Atom, dest: pointer, len: int): int {.nimcall.},
    writeData: proc(_: var Atom, toWrite: pointer, len: int): int {.nimcall.},
    setPos: proc(_: var Atom, pos: int) {.nimcall.},
    getPos: proc(_: Atom): int {.nimcall.},
    atEnd: proc(_: Atom): bool {.nimcall.}
  ]
  Stream* = AnyTraitor[StreamTrait]

  PrimitiveBase = concept pb
    pb.distinctBase is PrimitiveAtom
  PrimitiveAtom = SomeOrdinal or SomeFloat or enum or bool or char
  PrimitiveField = PrimitiveAtom or PrimitiveBase

  PrimitiveObject = concept type PO
    for field in default(PO).fields:
      field is PrimitiveField

  Array[T] = concept arr
    arr is array
    for x in arr.items:
      x is T

  Primitive = PrimitiveField or PrimitiveObject or Array[PrimitiveField or PrimitiveObject]

implTrait StreamTrait

proc read*(strm: var Stream, T: typedesc[Primitive]): T =
  mixin readData
  let read = strm.readData(result.addr, sizeof(T))
  if read != sizeof(T):
    raise newException(ValueError, "Did not fully read data, only read: " & $read)

proc read*(strm: var Stream, maxAmount: int): string =
  mixin readData
  result = newString(maxAmount)
  result.setLen(strm.readData(result[0].addr, maxAmount))

proc write*(strm: var Stream, data: Primitive): int =
  mixin writeData
  strm.writeData(data.addr, sizeof(data))

proc write*(strm: var Stream, data: string): int =
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

when isMainModule:
  if true:
    var a = StringStream(data: "Hello") # Statically dispatched
    assert a.read(array[5, char]) == "Hello"
    a.setPos(0)
    assert a.read(5) == "Hello"
    discard a.write(", World!")
    a.setPos(0)
    assert a.read(array[13, char]) == "Hello, World!"
    a.setPos(0)
    assert a.read(array[13, char]) == "Hello, World!"

  if true:
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

