import ../traitor/streams
import std/unittest

suite "Streams":
  test "Static Dispatch":
    var ss = StringStream(data: "Hello") # Statically dispatched
    check ss.read(array[5, char]) == "Hello"
    ss.setPos(0)
    check ss.read(5) == "Hello"
    discard ss.write(", World!")
    ss.setPos(0)
    check ss.read(array[13, char]) == "Hello, World!"
    ss.setPos(0)
    check ss.read(array[13, char]) == "Hello, World!"

    var fs = FileStream.init("/tmp/test.txt", fmReadWrite)
    discard fs.write"Hello"
    fs.setPos(0)
    check fs.read(array[5, char]) == "Hello"
    fs.setPos(0)
    check fs.read(5) == "Hello"
    discard fs.write(", World!")
    fs.setPos(0)
    check fs.read(array[13, char]) == "Hello, World!"
    fs.setPos(0)
    check fs.read(array[13, char]) == "Hello, World!"

  test "Dynamic Dispatch":
    var strms = [StringStream().toTrait StreamTrait, FileStream.init("/tmp/test2.txt", fmReadWrite).toTrait StreamTrait]
    for strm in strms.mitems:
      discard strm.write "Hello"
      strm.setPos(0)
      check strm.read(array[5, char]) == "Hello"
      strm.setPos(0)
      check strm.read(5) == "Hello"
      discard strm.write(", World!")
      strm.setPos(0)
      check strm.read(array[13, char]) == "Hello, World!"
      strm.setPos(0)
      check strm.read(array[13, char]) == "Hello, World!"
