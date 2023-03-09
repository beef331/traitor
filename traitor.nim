import std/[macros, macrocache, strformat, genasts, sugar, algorithm, enumerate, tables, sets]

type 
  TraitorConvDefect = object of Defect
  TraitorObj[T: static array] = object
    traceProc: proc(data, env: pointer){.nimcall.}
    destructorProc: proc(data: pointer){.nimcall.}
    vTable: ptr seq[pointer]
    idBacker: int # To allow typechecking at runtime
    obj: pointer

  TraitEntry = distinct NimNode

type Traitor[T: static array] = typeof(new TraitorObj[T])


proc `=destroy`[T](traitorObj: var TraitorObj[T]) =
  if traitorObj.obj != nil:
    traitorObj.destructorProc(traitorObj.obj)
    dealloc(traitorObj.obj)

proc `=trace`[T](traitorObj: var TraitorObj[T], env: pointer) =
  if traitorObj.obj != nil:
    traitorObj.traceProc(traitorObj.obj, env)

proc id(traitEntry: TraitEntry): NimNode = NimNode(traitEntry)[0]
proc names(traitEntry: TraitEntry): NimNode = NimNode(traitEntry)[1]

iterator procs(traitEntry: TraitEntry): NimNode =
  for x in NimNode(traitEntry)[2]:
    yield x

iterator idType(traitEntry: TraitEntry): (int, NimNode) =
  for val in NimNode(traitEntry)[4].pairs:
    yield val

proc procCount(traitEntry: TraitEntry): int = NimNode(traitEntry)[2].len
proc procIndex(traitEntry: TraitEntry, name: NimNode): int =
  for i, x in NimNode(traitEntry)[2]:
    if x.eqIdent name:
      return i

proc vtable(traitEntry: TraitEntry): NimNode = NimNode(traitEntry)[3]
proc typeId(traitEntry: TraitEntry, theType: NimNode, errorIfNotFound = false): int =
  for i, x in traitEntry.idType:
    if x.sameType(theType):
      return i
  if errorIfNotFound:
    error("Cannot get get a type id for given type", theType)
  else:
    result = NimNode(traitEntry)[4].len
    NimNode(traitEntry)[4].add theType


const
  traitTable = CacheSeq"TraitorTraitTable"##[
    TraitEntry is defined as the following
    TraitId - An array of integers which represent the type ID
    TraitNames - An array of the typedesc which created this Trait
    Procs - Name of procs and their types
    VTableName - A symbol to the vtable
    TypeNames - Array of symbols to fetch the id for traits
  ]##
  ids = CacheSeq"TraitorIdSeq"
  idCount = CacheCounter"TraitorId"

proc isSelf*(n: NimNode): bool =
  case n.kind
  of nnkIdent, nnkSym:
    n.eqIdent"Self"
  else:
    n[0].isSelf()


proc isValidConcept(t: NimNode): bool =
  let impl = t.getImpl[^1]
  result = impl.kind == nnkTypeClassTy
  if result:
    for prc in impl[^1]:
      if not prc.params[1][^2].isSelf:
        error("First parameter should be type `Self`.", prc.params[1][^2])
        result = false
        break


proc getOrAddId(desc: NimNode): int =
  if not desc.isValidConcept:
    error("Provided a type which is not a valid concept.", desc)
  for i, id in enumerate ids:
    if desc.sameType(id):
      return i

  result = idCount.value()
  ids.add desc
  inc idCount

proc replaceSelf(node, with: NimNode) =
  for i, n in node:
    if n.kind == nnkSym and n.eqIdent"Self":
      node[i] = with
    else:
      replaceSelf(n, with)

proc removeVarSelf(node: NimNode) =
  for i, n in node:
    if n.kind == nnkVarTy and n[0].kind == nnkSym and n[0].eqIdent"Self":
      node[i] = n[0]
    else:
      removeVarSelf(n)

proc getProcs(concepts: NimNode): NimNode =
  result = nnkBracketExpr.newTree()

  var convertedProcs: seq[NimNode]

  for concpt in concepts:
    for prc in concpt.getImpl[^1][^1]:
      let checking = prc.copyNimTree
      checking.replaceSelf(getType(int))
      block search:
        for x in convertedProcs:
          if checking.sameType(x):
            break search
        result.add prc
        convertedProcs.add checking

proc getTraitEntry(conceptId: NimNode,  concepts = NimNode(nil)): (TraitEntry, bool) =
  for traitEntry in traitTable:
    for i, x in traitEntry[0]:
      if conceptId[i] != x:
        break
    return (TraitEntry(traitEntry), false)

  if concepts == nil:
    error("Concept is not registered yet", conceptId)


  result[0] =
    TraitEntry(
      newStmtList(
        conceptId,
        concepts,
        getProcs(concepts),
        gensym(nskVar, "TraitorTable"),
        newStmtList()
      )
    )
  result[1] = true

  traitTable.add NimNode result[0]

macro isType(traitor: Traitor, res: typed): untyped =
  let
    ids = traitor.getTypeInst()
    (traitEntry, _) = getTraitEntry(ids)
    theId = traitEntry.typeId(res.getTypeInst(), errorIfNotFound = true)

  result = genAst(traitor, theId):
    traitor.idBacker == theId

macro traitorImpl(descs: varargs[typed]): untyped =
  if descs.len == 0:
    error("Did not provide any types to `implObj`.")

  result = nnkBracket.newTree()
  for desc in descs:
    result.add newLit getOrAddId(desc)

  result = nnkBracketExpr.newTree(bindSym"Traitor", result)

macro toTraitor(val: typed, traits: varargs[typed]): untyped =

  let id = nnkBracket.newTree()

  for x in traits:
    id.add newLit x.getOrAddId()

  let
    (traitorEntry, addedVtable) = getTraitEntry(id, traits)
    typ = val.getTypeInst()
    typId = traitorEntry.typeId(typ)
    theVtable = traitorEntry.vtable

  result = newStmtList()
  if addedVtable:
    result.add:
      genast(theVtable):
        var theVtable {.global.}: seq[pointer]
  else:
    result.add:
      genast(typId, theVtable, procCount = traitorEntry.procCount):
        theVtable.setLen(max(theVtable.len, procCount * typId))

  for i, prc in enumerate traitorEntry.procs:
    let ptyp = nnkProcTy.newTree(prc[3].copyNimTree, nnkPragma.newTree(ident"nimcall"))

    ptyp.replaceSelf(typ)
    result.add:
      genAst(
        typ,
        ptyp,
        id,
        typId,
        theVtable,
        name = ident($prc[0]),
        procCount = traitorEntry.procCount,
        index = newLit(i)
      ):
        theVtable.setLen(max(typId + 1 * procCount, theVtable.len))
        if theVtable[procCount * typId + index] == nil:
          theVtable[procCount * typId + index] = (ptyp)(name)

  result.add:
    genast(val, id, typId, theVtable, typ):
        let data =
          when val is ref:
            GcRef(typ)
            cast[pointer](val)
          elif val is ptr:
            cast[pointer](val)
          else:
            let thePtr = create(typeof(val))
            thePtr[] = val
            thePtr

        const
          theDestructor = proc(data: pointer) {.nimcall.} =
            `=destroy`(cast[ptr typ](data)[])
          theTracer = proc(data, env: pointer) {.nimcall.} =
            `=trace`(cast[ptr typ](data)[], env)
        Traitor[id](
          idBacker: typId,
          obj: data,
          vtable: theVtable.addr,
          destructorProc: theDestructor,
          traceProc: theTracer
        )


{.experimental: "dotOperators".}
macro `.`*(traitor: Traitor, procName: untyped, args: varargs[typed]): untyped =
  let
    id = traitor.getTypeInst[^1]
    (traitorEntry, _) = id.getTraitEntry()
    theVtable = traitorEntry.vtable
  for i, x in enumerate traitorEntry.procs:
    if x[0].eqIdent(procName):
      let callTyp = nnkProcTy.newTree(x[3].copyNimTree, nnkPragma.newTree(ident"nimcall"))
      callTyp.removeVarSelf()
      callTyp.replaceSelf(getType(pointer))

      result =
        genAst(traitor, callTyp, theVtable, id = newLit(i), procCount = traitorEntry.procCount()):
          cast[callTyp](theVtable[id + traitor.idBacker * procCount])(traitor.obj)
      for arg in args:
        result.add arg

macro getName*(traitor: Traitor): untyped =
  let
    ids = traitor.getTypeInst()
    (traitEntry, _) = getTraitEntry(ids)
  result = nnkCaseStmt.newTree()
  result.add nnkDotExpr.newTree(traitor, ident"idBacker")
  for i, x in traitEntry.idType:
    result.add nnkOfBranch.newTree(newLit i, newLit repr(x))

  result.add nnkElse.newTree(newLit"Unknown Type")


template `as`*(traitor: Traitor, desc: typedesc): auto =
  const res {.gensym.} = default(desc)
  if not traitor.isType(res):
    raise (ref TraitorConvDefect)(msg: "Cannot convert object from type")

  cast[ptr desc](traitor.obj)[]

proc isOf*(traitor: Traitor, desc: typedesc): bool =
  var a: desc
  traitor.isType(a)


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

proc `=destroy`(myObj: var MyObj) =
  echo myObj, " destroyed."


proc getBounds(a: var MyOtherObj, b: int): (int, int, int, int) = (10, 20, 30, 40 * b)
proc doOtherThing(a: MyOtherObj): int = 300
proc quack(a: var MyOtherObj) =
  a.a = 233

proc getBounds(a: var MyObj, b: int): (int, int, int, int) =
  result = (a.x, a.y, a.z, a.w * b)
  a.x = 100
  a.y = 300

proc doOtherThing(a: MyObj): int = a.y * a.z * a.w

proc quack(a: var MyObj) = a.x = 300


proc getBounds(a: var MyRef, b: int): (int, int, int, int) =
  result = (3, 2, 1, 30)
  # It's a ptr to a ptr it seems so this doesnt work
  a.a = 300

proc doOtherThing(a: MyRef): int = 300

proc quack(a: var MyRef) = a.a = 10

converter toQuackers[T: DuckObject](ducker: T): traitorImpl(DuckObject) = ducker.toTraitor(DuckObject)

proc main() =
  var a: traitorImpl(BoundObject, DuckObject)
  var b = MyObj(x: 100, y: 200)

  let c = [b.toQuackers, MyOtherObj(a: 0)]
  for x in c:
    x.quack()
    if x.isOf MyObj:
      echo x as MyObj
    elif x.isOf MyOtherObj:
      echo x as MyOtherObj
    echo x.getName()


  echo c[0] as MyObj
  echo c[1] as MyOtherObj


main()
