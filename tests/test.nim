import ../traitor
import std/unittest
type 
  BoundObject* = distinct tuple[
    getBounds: proc (a: var Atom, b: int): (int, int, int, int){.nimcall.},
    doOtherThing: proc(a: Atom): int {.nimcall.}]
  DuckObject* = distinct tuple[quack: proc(a: var Atom){.nimcall.}]

type
  MyObj = object
    x, y, z, w: int
  MyOtherObj = object
    a: byte
  MyRef = ref object
    a: int

implTrait BoundObject
implTrait DuckObject

proc getBounds(a: var MyOtherObj, b: int): (int, int, int, int) = (10, 20, 30, 40 * b)
proc doOtherThing(a: MyOtherObj): int = 300
proc quack(a: var MyOtherObj) = a.a = 233

proc getBounds(a: var MyObj, b: int): (int, int, int, int) =
  result = (a.x, a.y, a.z, a.w * b)
  a.x = 100
  a.y = 300

proc doOtherThing(a: MyObj): int = a.y * a.z * a.w

proc quack(a: var MyObj) = discard


proc getBounds(a: var MyRef, b: int): (int, int, int, int) =
  result = (3, 2, 1, 30)
  # It's a ptr to a ptr it seems so this doesnt work
  a.a = 300

proc doOtherThing(a: MyRef): int = 300

proc quack(a: var MyRef) = a.a = 10

emitConverter MyObj, BoundObject
emitConverter MyObj, DuckObject
emitConverter MyOtherObj, BoundObject
emitConverter MyOtherObj, DuckObject
emitConverter MyRef, BoundObject
emitConverter MyRef, DuckObject

var
  valA = MyObj(x: 0, y: 10, z: 30, w: 100)
  valB = MyOtherObj()
  valC = MyRef()
  valD = MyOtherObj()

type MyLateType  = object
  a, b, c: int

proc getBounds(a: var MyLateType, b: int): (int, int, int, int) = discard
proc doOtherThing(a: MyLateType): int = discard
proc quack(a: var MyLateType) = a.a = 300
emitConverter MyLateType, BoundObject
emitConverter MyLateType, DuckObject

test "Basic data logic":
  var myData = [Traitor[BoundObject] valA, valB, valC, valD, MyLateType(a: 300)]
  check myData[0].getData(MyObj) == MyObj(x: 0, y: 10, z: 30, w: 100)
  for x in myData.mitems:
    if x of BoundObject.typedTo(MyObj):
      check x.getData(MyObj).x == 0
      check x.getBounds(3) == (0, 10, 30, 300)
      let myObj = x.getData(MyObj)
      check x.doOtherThing() == myObj.y * myObj.z * myObj.w
    elif x of BoundObject.typedTo(MyRef):
      check x.getBounds(3) == (3, 2, 1, 30)
    elif x of BoundObject.typedTo(MyOtherObj):
      check x.getBounds(3) == (10, 20, 30, 120)
      check x.doOtherThing() == 300
  
  check myData[0].getData(MyObj) == MyObj(x: 100, y: 300, z: 30, w: 100)
  check myData[2].getData(MyRef) == valC # Check the ref is the same

test "Duck testing":
  var myQuackyData = [Traitor[DuckObject] valA, valB, valC, valD, MyLateType(a: 50)]

  for x in myQuackyData.mitems:
    x.quack()

  check myQuackyData[1].getData(MyOtherObj) == MyOtherObj(a: 233)
  myQuackyData[1].getData(MyOtherObj).a = 100
  check myQuackyData[1].getData(MyOtherObj) == MyOtherObj(a: 100) # Tests if field access works
  check myQuackyData[^1].getData(MyLateType).a == 300
