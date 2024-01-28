import benchy

type
  MyObject = ref object of RootObj
    data: int
  Child = ref object of MyObject
    otherData: float
  ChildChild = ref object of MyObject
    othererData: string
  ChildChildChild = ref object of MyObject
    hmm: float
  ChildChildChildChild = ref object of MyObject
    huh: string

method doThing(obj: MyObject) {.base.} = obj.data += 1
method doThing(obj: Child) = obj.data += 1
method doThing(obj: ChildChild) = obj.data += 1
method doThing(obj: ChildChildChild) = obj.data += 1
method doThing(obj: ChildChildChildChild) = obj.data += 1

const
  iterations {.intdefine.} = 100
  collSize {.intDefine.} = 1500000

template inheritanceBench(typ: typedesc) =
  if true:
    var objData = newSeq[typ](collSize)
    for x in objData.mitems:
      new x
    timeit $typ & " Nim Method", iterations:
      for x in objData:
        doThing(x)

inheritanceBench MyObject
inheritanceBench Child
inheritanceBench ChildChild
inheritanceBench ChildChildChild
inheritanceBench ChildChildChildChild

if true:
  var objData = newSeq[MyObject](collSize)
  for i, x in objData.mPairs:
    case i mod 5
    of 0:
      x = MyObject()
    of 1:
      x = Child()
    of 2:
      x = ChildChild()
    of 3:
      x = ChildChildChild()
    else:
      x = ChildChildChildChild()
  timeit "All Nim Method", iterations:
    for x in objData:
      doThing(x)

import ../traitor

type
  Obj1 = object
    data: int
  Obj2 = object
    data: int
    otherData: float
  Obj3 = object
    data: int
    otherData: float
    othererData: string
  Obj4 = object
    data: int
    otherData: float
    othererData: string
    hmm: float

  Obj5 = object
    data: int
    otherData: float
    othererData: string
    hmm:float
    huh: string

  Thinger = distinct tuple[doThing: proc(_: var Atom) {.nimcall.}]

proc doThing[T: Obj1 or Obj2 or Obj3 or Obj4 or Obj5](obj: var T) = obj.data += 1

implTrait Thinger

template traitDispatch(typ: typedesc) =
  if true:
    var objData = newSeq[Traitor[Thinger]](collSize)
    for x in objData.mitems:
      x = default(typ)
    timeit $typ & " Traitor", iterations:
      for x in objData.mitems:
        doThing(x)

template staticDispatch(typ: typedesc) =
  if true:
    var objData = newSeq[typ](collSize)
    timeit $typ & " static dispatch", iterations:
      for x in objData.mitems:
        doThing(x)

traitDispatch Obj1
traitDispatch Obj2
traitDispatch Obj3
traitDispatch Obj4
traitDispatch Obj5


if true:
  var objData = newSeq[Traitor[Thinger]](collSize)
  for i, x in objData.mPairs:
    case i mod 5
    of 0:
      x = Obj1()
    of 1:
      x = Obj2()
    of 2:
      x = Obj3()
    of 3:
      x = Obj4()
    else:
      x = Obj5()
  timeit "All Traitor Dispatch", iterations:
    for x in objData.mitems:
      doThing(x)



staticDispatch Obj1
staticDispatch Obj2
staticDispatch Obj3
staticDispatch Obj4
staticDispatch Obj5
