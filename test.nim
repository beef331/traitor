import traitor
type 
  BoundObject* = concept
    proc getBounds(a: var Self, b: int): (int, int, int, int)
    proc doOtherThing(a: Self): int
  DuckObject* = concept
    proc quack(a: var Self)

type
  MyObj = object
    x, y, z, w: int
  MyOtherObj = object
    a: byte
  MyRef = ref object
    a: int

MyOtherObj.implements BoundObject, DuckObject
MyObj.implements BoundObject, DuckObject
MyRef.implements BoundObject, DuckObject

emitConverters(
  BoundObject,
  DuckObject,
  [BoundObject, DuckObject]
  )

proc getBounds(a: var MyOtherObj, b: int): (int, int, int, int) {.impl.} = (10, 20, 30, 40 * b)
impl:
  proc doOtherThing(a: MyOtherObj): int = 300
  proc quack(a: var MyOtherObj) = a.a = 233


let valD = MyOtherObj()


impl:
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

checkImpls()

var
  valA = MyObj(x: 0, y: 10, z: 30, w: 100)
  valB = MyOtherObj()
  valC = MyRef()
  
  
var myData = [valA.toImpl BoundObject, valB, valC, valD]

for x in myData.mitems:
  if x of MyObj:
    var myObj = x as MyObj
    assert myObj.x == 0
    assert x.getBounds(3) == (valA.x, valA.y, valA.z, valA.w * 3)
    myObj = x as MyObj
    assert x.doOtherThing() == myObj.y * myObj.z * myObj.w
  elif x of MyRef:
    assert x.getBounds(3) == (3, 2, 1, 30)
  elif x of MyOtherObj:
    assert x.getBounds(3) == (10, 20, 30, 120)
    assert x.doOtherThing() == 300

assert (myData[0] as MyObj) == MyObj(x: 100, y: 300, z: 30, w: 100)


var myQuackyData = [valA.toImpl(BoundObject, DuckObject), valB, valC, valD]

for x in myQuackyData.mitems:
  discard x.doOtherThing()
  x.quack()
assert myData[2] as MyRef == valC
assert myQuackyData[1] as MyOtherObj == MyOtherObj(a: 233)