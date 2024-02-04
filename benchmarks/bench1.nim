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

const collSize {.intDefine.} = 1500000


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

import criterion
var cfg = newDefaultConfig()

when defined(useCriterion):
  proc `$`(thing: MyObject): string =
    if thing of ChildChildChildChild:
      $ChildChildChildChild
    elif thing of ChildChildChild:
      $ChildChildChild
    elif thing of ChildChild:
      $ChildChild
    elif thing of Child:
      $Child
    else:
      $MyObject

  proc `$`(thing: Traitor[Thinger]): string =
    if thing of TypedTraitor[Obj1, Thinger]:
      $Obj1
    elif thing of TypedTraitor[Obj2, Thinger]:
      $Obj2
    elif thing of TypedTraitor[Obj3, Thinger]:
      $Obj3
    elif thing of TypedTraitor[Obj4, Thinger]:
      $Obj4
    else:
      $Obj5


  benchmark cfg:
    proc methodDispatch(obj: MyObject) {.measure: [MyObject(), Child(), ChildChild(), ChildChildChild(), ChildChildChildChild()].} =
      doThing(obj)

    proc allMethodDispatch(val: openArray[MyObject]) {.measure: [[MyObject(), Child(), ChildChild(), ChildChildChild(), ChildChildChildChild()]].} =
      for item in val:
        doThing(item)

    proc traitDispatch(val: Traitor[Thinger]) {.measure:[Obj1().toTrait(Thinger), Obj2().toTrait(Thinger), Obj3().toTrait(Thinger), Obj4().toTrait(Thinger), Obj5().toTrait(Thinger)].} =
      doThing(val)

    proc allTraitDispatch(val: openArray[Traitor[Thinger]]) {.measure:[[Obj1().toTrait(Thinger), Obj2().toTrait(Thinger), Obj3().toTrait(Thinger), Obj4().toTrait(Thinger), Obj5().toTrait(Thinger)]].} =
      for item in val:
        doThing(item)
else:

  when defined(useBenchy):
    import benchy
  else:
    import std/[times, monotimes]
    template timeit(msg: string, runs: int, body: untyped): untyped =
      var
        acc: Duration
        lowest = Duration.high
        highest = Duration.low

      for _ in 0..<runs:
        let start = getMonoTime()
        body
        let diff = getMonoTime() - start
        lowest = min(diff, lowest)
        highest = max(diff, highest)
        acc += diff

      echo msg, ":\navg: ", acc div runs, "\nmin: ", lowest, "\nmax: ", highest


  proc main() =
    proc inheritanceDispatch(typ: typedesc) =
      var objData = newSeq[MyObject](collSize)
      for item in objData.mitems:
        item = typ()
      timeit "Method " & $typ, 100:
        for item in objData:
          doThing(item)

    proc traitDispatch(typ: typedesc) =
      var objData = newSeq[Traitor[Thinger]](collSize)
      for item in objData.mitems:
        item = typ().toTrait(Thinger)
      timeit "Traitor " & $typ, 100:
        for item in objData:
          doThing(item)

    proc allMethodDispatch() =
      var objData = newSeq[MyObject](collSize)
      for i, item in objData.mpairs:
        case i mod 5
        of 0:
          item = MyObject()
        of 1:
          item = Child()
        of 2:
          item = ChildChild()
        of 3:
          item = ChildChildChild()
        else:
          item = ChildChildChild()

      timeit "Method all", 100:
        for item in objData:
          doThing(item)

    proc allTraitDispatch() =
      var objData = newSeq[Traitor[Thinger]](collSize)
      for i, item in objData.mpairs:
        case i mod 5
        of 0:
          item = Obj1().toTrait Thinger
        of 1:
          item = Obj2().toTrait Thinger
        of 2:
          item = Obj3().toTrait Thinger
        of 3:
          item = Obj4().toTrait Thinger
        else:
          item = Obj5().toTrait Thinger

      timeit "Traitor all", 100:
        for item in objData:
          doThing(item)


    inheritanceDispatch MyObject
    inheritanceDispatch Child
    inheritanceDispatch ChildChild
    inheritanceDispatch ChildChildChild
    inheritanceDispatch ChildChildChildChild
    allMethodDispatch()



    traitDispatch Obj1
    traitDispatch Obj2
    traitDispatch Obj3
    traitDispatch Obj4
    traitDispatch Obj5
    allTraitDispatch()

  main()


implTraitProcs()
