import nimterface
type 
  BoundObject* = concept
    proc getBounds(a: var Self, b: int): (int, int, int, int)
    proc doOtherThing(a: Self): int
  DuckObject* = concept
    proc quack(a: Self)

type
  MyObj = object
    x, y, z, w: int
  MyOtherObj = object
  MyRef = ref object
    a: int


MyOtherObj.impl(BoundObject)
MyOtherObj.impl(DuckObject)


MyObj.impl(BoundObject)
MyObj.impl(DuckObject)


MyRef.impl(BoundObject)
MyRef.impl(DuckObject)



proc getBounds(a: var MyOtherObj, b: int): (int, int, int, int) {.impl.} = (10, 20, 30, 40 * b)
proc doOtherThing(a: MyOtherObj): int {.impl.} = 300
proc quack(a: MyOtherObj) {.impl.} = echo "Hello"

let valD = MyOtherObj()



proc getBounds(a: var MyObj, b: int): (int, int, int, int) {.impl.} = 
  result = (a.x, a.y, a.z, a.w * b)
  a.x = 100
  a.y = 300

proc doOtherThing(a: MyObj): int {.impl.} = a.y * a.z * a.w

proc quack(a: MyObj) {.impl.} = echo a


proc getBounds(a: var MyRef, b: int): (int, int, int, int) {.impl.} = 
  result = (3, 2, 1, 30)
  a.a = 300

proc doOtherThing(a: MyRef): int {.impl.} = 300

proc quack(a: MyRef) {.impl.} = echo a[]


checkImpls()

proc test: MyRef =
  var
    valA = MyObj(x: 0, y: 10, z: 30, w: 100)
    valB = MyOtherObj()
    valC = MyRef()
    myData = [valA.toBoundObject, valB, valC, valD]
    myQuackyData = [
      valA.toImpl(BoundObject, DuckObject),
      valB.toImpl(BoundObject, DuckObject),
      valC.toImpl(BoundObject, DuckObject),
      valD.toImpl(BoundObject, DuckObject)]

  for x in myData.mitems:
    if x of MyObj:
      var myObj = x as MyObj
      assert myObj.x == 0
    echo x.getBounds(3)
    echo x.doOtherThing()
  
  for x in myQuackyData:
    echo x.doOtherThing()
    x.quack()

  var a = valA.toBoundObject
  echo a.getBounds(10)

  echo myData[0] as MyObj
  result = myData[2] as MyRef # This may leak?
  echo result.a

let a = test()
echo a.a
