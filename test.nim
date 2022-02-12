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


MyOtherObj.implements BoundObject, DuckObject
MyObj.implements BoundObject, DuckObject
MyRef.implements BoundObject, DuckObject



proc getBounds(a: var MyOtherObj, b: int): (int, int, int, int) {.impl.} = (10, 20, 30, 40 * b)
impl:
  proc doOtherThing(a: MyOtherObj): int = 300
  proc quack(a: MyOtherObj) = echo "Hello"

let valD = MyOtherObj()


impl:
  proc getBounds(a: var MyObj, b: int): (int, int, int, int) = 
    result = (a.x, a.y, a.z, a.w * b)
    a.x = 100
    a.y = 300

  proc doOtherThing(a: MyObj): int = a.y * a.z * a.w

  proc quack(a: MyObj)  = echo a


  proc getBounds(a: var MyRef, b: int): (int, int, int, int) =
    result = (3, 2, 1, 30)
    # It's a ptr to a ptr it seems so this doesnt work
    a.a = 300

  proc doOtherThing(a: MyRef): int = 300

  proc quack(a: MyRef) = 
    echo a.repr
    a.a = 10
echo 10.toImpl(BoundObject, DuckObject)

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


  echo "Bound Data"
  for x in myData.mitems:
    if x of MyObj:
      var myObj = x as MyObj
      assert myObj.x == 0
    echo x.getBounds(3)
    echo x.doOtherThing()

  assert (myData[0] as MyObj) == MyObj(x: 100, y: 300, z: 30, w: 100)
  echo "\nQuacky Data"
  for x in myQuackyData:
    echo x.doOtherThing()
    x.quack()
  echo valC.repr
  echo "\n Dumb Data"
  var a = valA.toBoundObject
  echo a.getBounds(10)

  echo myData[0] as MyObj
  result = myData[2] as MyRef # This may leak?
  echo result.a

let a = test()
echo a[]
