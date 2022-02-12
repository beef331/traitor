import std/[macros, macrocache, strformat, genasts, strutils, sugar, algorithm, enumerate, tables]

type 
  ImplConvDefect = object of Defect
  ImplObj[PCount: static int; Conc: static seq[int]] = object
    vTable: array[PCount, pointer]
    idBacker: int # To allow typechecking at runtime
    obj: ptr UncheckedArray[byte]
  ConceptImpl = enum
    getTypeName, getTypeImpl

proc id*(impl: ImplObj): int = impl.idBacker


var implTable {.compileTime.} = CacheSeq"ConceptImplTable"

iterator conceptImpls(concepts: openArray[int], impl = getTypeName): (int, NimNode) =
  ## Yields `typeId`, `typeSym` for each impl that matches the `concepts`
  var actualId = 0
  for i, typ in implTable[concepts[0]][1..^1]:
    block searchType:
      let
        myType = typ[0]
        rangeLow = 
          if concepts.len == 1:
            0
          else:
            1

      for id in rangeLow..<concepts.len:
        for otherType in implTable[id]:
          if otherType[0] == myType:
            case impl
            of getTypeName:
              yield (actualId, otherType[0])
            of getTypeImpl:
              yield (actualId, otherType)

            inc actualId
            break searchType

proc sameParams(a, b: NimNode): bool =
  ## Checks if the parameters match types including `var/ptr/ref`
  result = a.len == b.len
  if result:
    result = a[^2] == b[^2]
    if not result:
      if a[^2].kind in {nnkRefTy, nnkVarTy, nnkPtrTy} and a[^2].kind == b[^2].kind:
        result = a[^2][0].sameType(b[^2][0])
      else:
        result = a[^2].sameType b[^2]

proc sameProc(a, b: NimNode): bool =
  ## Checks if the two procedures match
  result = a[0].eqIdent(b[0]) and (a[3].len == b[3].len)
  if result:
    let
      aParams = a[3]
      bParams = b[3]
    for i, x in a[3]:
      if i == 0:
        result = aParams[0].sameType(bParams[0])
      else:
        result = sameParams(x, bParams[i])
      if not result: break



iterator procIds(concepts: NimNode): (int, NimNode) =
  ## returns `id`, `procName`
  assert concepts.kind == nnkBracket
  let concepts = collect(for x in concepts: int x.intVal)
  var
    yieldedProcs = initTable[string, seq[NimNode]]()
    ind = 0

  proc didYield(prc: NimNode): bool =
    let name = $prc[0]
    if name in yieldedProcs:
      for oldImpl in yieldedProcs[name]:
        if oldImpl.sameProc(prc):
          return true
      yieldedProcs[name].add prc
    else:
      yieldedProcs[name] = @[prc]

  for concpt in concepts:
    for impl in implTable[concpt][0][1]:
      if not didYield(impl):
        yield (ind, impl)
        inc ind



iterator conceptImpls(concepts: Nimnode, impl = getTypeName): (int, NimNode) =
  assert concepts.kind == nnkBracket
  let concepts = collect(for x in concepts: int x.intVal)
  for x in conceptImpls(concepts, impl):
    yield x

iterator conceptNames(concepts: openArray[int]): NimNode = 
  for concpt in concepts:
    yield implTable[concpt][0][0]

iterator conceptProcs(typ, concepts: NimNode): NimNode =
  ## returns `id`, `procName` for the given `typ`
  assert concepts.kind == nnkBracket
  let concepts = collect(for x in concepts: int x.intVal)
  var yieldedProcs = initTable[string, seq[NimNode]]()

  proc didYield(prc: NimNode): bool =
    let name = $prc[0]
    if name in yieldedProcs:
      for oldImpl in yieldedProcs[name]:
        if oldImpl.sameProc(prc):
          return true
      yieldedProcs[name].add prc
    else:
      yieldedProcs[name] = @[prc]

  for concpt in concepts:
    for impl in implTable[concpt][1..^1]:
      if impl[0] == typ:
        for prc in impl[1..^1]:
          if not didYield(prc[1]):
            yield prc[0]


iterator conceptNames(concepts: NimNode): NimNode =
  assert concepts.kind == nnkBracket
  let concepts = collect(for x in concepts: int x.intval)
  for concpt in conceptNames concepts:
    yield concpt

proc replaceSelf(n, replaceWith: NimNode) =
  ## Replaces are instances of `Self` with `replaceWith`
  for i, x in n:
    if x.kind == nnkSym:
      if x.eqIdent"Self":
        n[i] = replaceWith
    else:
      x.replaceSelf(replaceWith)


macro implements*(theType: typedesc, concepts: varargs[typed]) =
  ## Adds the implementation of concept `b` to the `implTable`
  for typ in concepts:
    let
      typImpl = typ.getImpl
      procs = typImpl[^1][^1]
    var newProcs = newSeqOfCap[NimNode](procs.len)
    for x in procs:
      let newProc = x.copyNimTree()
      newProc.replaceSelf(theType)
      newProcs.add nnkPar.newTree(newEmptyNode(), newProc) # each procedure is a `(sym, proc)`

    for concpt in implTable:
      if concpt[0][0] == typ:
        concpt.add newStmtList(theType)
        concpt[^1].add newProcs
        break
    implTable.add newStmtList(newStmtList(typ, procs), newStmtList(@[theType] & newProcs)) # stmtlist(conceptImpl(name, procs), par(typeImpl, procs)) is how the seq is laid out


proc markIfImpls(pDef, concpt: NimNode): (bool, NimNode) =
  ## Adds `pdef.name` to the `implTable` if it matches the desired impl
  ## returns list of newly fulfilled concepts, for converters to be made
  for iProc in concpt[0][^1]:
    for typImpl in concpt[1..^1]:
      let newTyp = iProc.copyNimTree
      newTyp.replaceSelf(typImpl[0])
      if newTyp.sameProc pDef:
        var
          fullyImplemented = 0
          implementedNewProc = false
        for impl in typImpl:
          if impl.kind == nnkPar:
            if impl[1].sameProc(pDef) and impl[0].kind == nnkEmpty:
              impl[0] = pDef[0]
              implementedNewProc = true
            if impl[0].kind == nnkSym:
              inc fullyImplemented
        return (fullyImplemented == typImpl.len - 1 and implementedNewProc, typImpl[0])


proc getProcs(val, cncpt: NimNode): seq[NimNode] =
  # Get all proc names for this concept
  for prc in conceptProcs(val.getTypeInst, cncpt):
    result.add prc

proc getProcIndexAndDef(val, concpt, name: NimNode): (NimNode, NimNode) =
  ## Gets the proc index and the definition of that proc
  for id, prc in procIds(concpt):
    if prc[0].eqIdent name:
      result = (newLit id, prc)
      break

proc getTypeId(val, cncpt: NimNode): int =
  ## Gets the concept id and type id
  result = -1
  let valTyp = getTypeInst(val)
  for (id, typ) in conceptImpls(cncpt):
    if typ == valTyp:
      result = id


macro checkImpls*() =
  ## Ensures all types implemenent the procedures, and if not shows all lacking matches
  var allMissings =""
  for concpts in implTable:
    for impl in concpts[1..^1]:
      if impl[^1].len > 1:
        var localMissings = ""
        for x in impl[1..^1]:
          if x[0].kind != nnkSym:
            let impl = nnkProcDef.newTree
            x[1].copyChildrenTo(impl)
            localMissings.add impl.repr
            localMissings.add "\n"
        if localMissings.len > 0:
          allMissings.add fmt("\nMissing impls for type: '{impl[0]}', to match '{concpts[0][0]}':\n{localMissings}")
  if allMissings.len > 0:
    error(allMissings)

macro impl*(pDef: typed): untyped =
  ## Adds `pdef` to `implTable` for all concepts that require it
  ## emits a convert if fully matched
  let pDefs =
    if pDef.kind == nnkProcDef:
      newStmtList(pDef)
    else:
      pDef
  result = newStmtList(pDef)
  for pDef in pdefs:
    if pdef.kind != nnkProcDef:
      error("Cannot implement a non procedure.", pdef)
    var
      i = 0
      implementsOnce = false
    for concpt in implTable:
      let (fullyImpls, typ) = markIfImpls(pDef, concpt)
      if pDef.kind != nnkEmpty:
        implementsOnce = true
      if fullyImpls:
        let
          conceptName = concpt[0][0]
          name = ident "to" & $conceptName
        result.add:
          genASt(name, i, size = concpt[0][1].len, typ, conceptName):
            converter name*(obj: typ): ImplObj[size, @[i]] = obj.toImpl(conceptName)
      inc i
    if not implementsOnce:
      error("Attempting to implement unknown proc.", pDef)

proc toId(typ: NimNode): NimNode =
  result = nnkBracket.newTree()
  var ids: seq[int]
  while ids.len < typ.len:
    for ind, x in enumerate implTable:
      if x[0][0] == typ[ids.len]:
        ids.add ind
        break
  ids.sort
  for id in ids:
    result.add newLit id

macro toImpl*(val: typed, constraint: varargs[typed]): untyped =
  ## Converts an object to the desired interface
  let
    conceptIds = constraint.toId()
    procs = getProcs(val, conceptIds)
    rawProcs = nnkBracket.newTree()
    typeId = val.getTypeId(conceptIds)
  for x in procs:
    rawProcs.add nnkCast.newTree(ident"pointer", x)
  result = genAst(rawProcs, pCount = procs.len, val, conceptIds, typeId):
    var
      data = cast[ptr UncheckedArray[byte]](createU(typeOf(val)))
      obj = val
    when val is ref:
      GC_Ref(val)
    copyMem(data[0].addr, obj.unsafeAddr, sizeof(val))
    ImplObj[pCount, @conceptIds](vtable: rawProcs, idBacker: typeId, obj: data)

macro ofImpl(val: ImplObj, b: typedesc): untyped =
  ## Does the internal logic for the `of` operator, checking if the id's match the desired type
  let
    inst = val.getTypeInst 
    concepts = inst[^1]
  var ind = 0
  for (id, typ) in conceptImpls(concepts):
    if typ == b:
      ind = id
      break

  result = genast(val, ind):
    val.id == ind


macro unrefObj(val: ImplObj): untyped =
  ## Unref's the object and destroys the object that it wraps
  let
    inst = val.getTypeInst
    concepts = collect:(for x in inst[^1]: int x.intVal)
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for (id, name) in conceptImpls(concepts):
    result.add:
      nnkOfBranch.newTree(newLit id):
        genAst(val, typ = name):
          when typ is ref:
            GC_UnRef(cast[ptr typ](val.obj)[])
          `=destroy`(cast[ptr typ](val.obj)[])
  result.add nnkElse.newTree(nnkDiscardstmt.newTree(newEmptyNode()))

macro ensureType(val: ImplObj, b: typedesc): untyped =
  ## Implements the type assurance that the types match, gives helpful mismatch message
  let
    inst = val.getTypeInst 
    concepts = collect(for x in inst[^1]: int x.intval)
    idTable = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for (id, typ) in conceptImpls(concepts):
    idTable.add:
      nnkOfBranch.newTree(newLit id, newLit fmt"'{val.repr}' is type '{typ.repr}' but wanted '{b.repr}'.")
  idTable.add nnkElse.newTree(newLit("Unexpected type ID"))

  result = genast(val, idTable, ofOp = ofImpl, b):
    if not ofOp(val, b):
      raise newException(ImplConvDefect, idTable)

proc `=destroy`[Count: static int; Conc: static seq[int]](obj: var ImplObj[Count, Conc]) =
  unrefObj(obj)

macro isPtr(val: ImplObj): untyped =
  let
    inst = val.getTypeInst 
    concepts = collect(for x in inst[^1]: int x.intval)
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for (id, typ) in conceptImpls(concepts):
    result.add:
      nnkOfBranch.newTree(newLit id):
        genast(val, typ):
          typ is (ref or ptr)
  result.add nnkElse.newTree(newLit true)
  echo result.repr


{.experimental: "dotOperators".}

macro `.()`*(val: ImplObj, field: untyped, args: varargs[untyped]): untyped =
  ## Implements the logic for UFCS calls so nothing annoying is required to call the procedures
  let
    inst = val.getTypeInst
    (ind, def) = getProcIndexAndDef(val, inst[^1], field)
    pTy = nnkProcTy.newTree()
  if nnkNilLit in {ind.kind, def.kind}:
    let mismatch = block:
      var
        msg = ""
        count = 0
      for x in conceptNames inst[^1]:
        msg.add $x
        if count < inst.len - 2:
          msg.add "',' "
        inc count
      msg
    error(fmt"'{field}' proc not found for concept: '{mismatch}'.", field)

  let
    isPtrObj = def[3][1][^2].typeKind == ntyVar

  case val.kind
  of nnkHiddenDeref:
    discard # might need to handle this if it's a non pointer
  of nnkSym:
    if val.symKind != nskVar and isPtrObj:
      error(fmt"'{field}' requires a 'var', but passed variable was immutable.", val)
  else:
    discard

  pTy.add def[3].copyNimTree
  pTy.add nnkPragma.newTree(ident"nimcall")
  pTy[0][1][^2] =
    genAst():
      pointer


  let prc = genSym(nskLet, $field)

  result = newStmtList():
    genast(ind, val, pTy, prc):
      let prc = cast[pTy](val.vtable[ind])

  result.add newCall(prc)
  echo val.treeRepr, " ", isPtrObj
  result[^1].add:
    if isPtrObj:
      genAst(val):
        val.obj
    else:
      genAst(val):
        if isPtr(val):
          let pntr = cast[ptr UncheckedArray[int]](val.obj)[0]
          cast[pointer](pntr)
        else:
          cast[pointer](val.obj)

  for arg in args:
    result[^1].add arg
  echo result.repr


template `of`*(implObj: ImplObj, T: typedesc): bool =
  ofImpl(implObj, T)

template `as`*(implObj: ImplObj, T: typedesc): untyped =
  ensureType(implObj, T)
  when T is ref:
    let val = cast[ptr T](implObj.obj)[]
    Gc_Ref(val)
    val
  else:
    cast[ptr T](implObj.obj)[]