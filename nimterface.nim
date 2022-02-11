import std/[macros, macrocache, strformat, genasts, strutils]

type 
  ImplConvDefect = object of Defect
  ImplObj[PCount, Conc: static int] = object
    vTable: array[PCount, pointer]
    idBacker: int # To allow typechecking at runtime
    obj: ptr UncheckedArray[byte]

proc id*(impl: ImplObj): int = impl.idBacker


var implTable {.compileTime.} = CacheSeq"ConceptImplTable"

proc replaceSelf(n, replaceWith: NimNode) =
  ## Replaces are instances of `Self` with `replaceWith`
  for i, x in n:
    if x.kind == nnkSym:
      if x.eqIdent"Self":
        n[i] = replaceWith
    else:
      x.replaceSelf(replaceWith)


macro impl*(a: typedesc, b: typedesc) =
  ## Adds the implementation of concept `b` to the `implTable`
  let
    bImpl = b.getImpl
    procs = bImpl[^1][^1]
  var newProcs = newSeqOfCap[NimNode](procs.len)
  for x in procs:
    let newProc = x.copyNimTree()
    newProc.replaceSelf(a)
    newProcs.add nnkPar.newTree(newEmptyNode(), newProc) # each procedure is a `(sym, proc)`

  for concpt in implTable:
    if concpt[0][0] == b:
      concpt.add newStmtList(a)
      concpt[^1].add newProcs
      return
  implTable.add newStmtList(newStmtList(b, procs), newStmtList(@[a] & newProcs)) # stmtlist(conceptImpl(name, procs), par(typeImpl, procs)) is how the seq is laid out


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

  error("Attempting to implement unknown proc.", pDef)

proc getProcs(val, cncpt: NimNode): seq[NimNode] =
  # Get all proc names for this concept
  for impl in implTable:
    if impl[0][0] == cncpt:
      for impls in impl[1..^1]:
        if impls[0] == val.getTypeInst:
          for x in impls[1..^1]:
            result.add x[0]

proc getProcIndexAndDef(val, cncpt, name: NimNode): (NimNode, NimNode) =
  ## Gets the proc index and the definition of that proc
  for impl in implTable[int cncpt.intval][1..^1]:
    for i, impls in impl[1..^1]:
      if impls[0].eqIdent(name):
        return (newLit i, impls[1].copyNimTree)

proc getTypeId(val, cncpt: NimNode): (int, int) =
  ## Gets the concept id and type id
  result = (-1, -1)
  let valTyp = getTypeInst(val)
  var i = 0
  for impl in implTable:
    if impl[0][0].eqIdent cncpt:
      for j, typ in impl[1..^1]:
        if typ[0] == valTyp:
          return (j, i)
    inc i


macro checkImpls*() =
  ## Ensures all types implemenent the procedures, and if not shows all lacking matches
  for concpts in implTable:
    for impl in concpts[1..^1]:
      if impl[^1].len > 1:
        var missing = ""
        for x in impl[1..^1]:
          if x[0].kind != nnkSym:
            let impl = nnkProcDef.newTree
            x[1].copyChildrenTo(impl)
            missing.add impl.repr
            missing.add "\n"
        if missing.len > 0:
          error(fmt("Missing impls for type: '{impl[0]}', to match '{concpts[0][0]}':\n{missing}"))

macro impl*(pDef: typed): untyped =
  ## Adds `pdef` to `implTable` for all concepts that require it
  ## emits a convert if fully matched
  var i = 0
  for concpt in implTable:
    let (fullyImpls, typ) = markIfImpls(pDef, concpt)
    if fullyImpls:
      let
        conceptName = concpt[0][0]
        name = ident "to" & $conceptName
      result = newStmtList(pDef):
        genASt(name, i, size = concpt[0].len, typ, conceptName):
          converter name*(obj: typ): ImplObj[size, i] = obj.toImpl(conceptName)
    inc i
  echo result.repr

macro toImpl*(val: typed, constraint: typedesc): untyped =
  ## Converts an object to the desired interface
  let
    procs = getProcs(val, constraint)
    rawProcs = nnkBracket.newTree()
    (typeId, conceptId) = val.getTypeId(constraint)
  for x in procs:
    rawProcs.add nnkCast.newTree(ident"pointer", x)

  result = genAst(rawProcs, pCount = procs.len, val, conceptId, typeId):
    let
      data = cast[ptr UncheckedArray[byte]](alloc(sizeof(val)))
      obj = val
    when val is ref:
      GC_Ref(obj)
    copyMem(data[0].addr, obj.unsafeAddr, sizeof(val))
    ImplObj[pCount, conceptId](vtable: rawProcs, idBacker: typeId, obj: data)


macro ofImpl(val: ImplObj, b: typedesc): untyped =
  ## Does the internal logic for the `of` operator, checking if the id's match the desired type
  let
    inst = val.getTypeInst 
    cncpt = int inst[^1].intval
  var ind = -1
  for i, typ in implTable[cncpt][1..^1]:
    if typ[0] == b:
      ind = i
      break

  result = genast(val, ind):
    val.id == ind

macro unrefObj(val: ImplObj): untyped =
  ## Unref's the object and destroys the object that it wraps
  let
    inst = val.getTypeInst
    cncpt = int inst[^1].intVal
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for i, typ in implTable[cncpt][1..^1]:
    result.add:
      nnkOfBranch.newTree(newLit i):
        genAst(val, typ = typ[0]):
          when typ is ref:
            GC_UnRef(cast[ptr typ](val.obj)[])
          `=destroy`(cast[ptr typ](val.obj)[])
  result.add nnkElse.newTree(nnkDiscardstmt.newTree(newEmptyNode()))

macro ensureType(val: ImplObj, b: typedesc): untyped =
  ## Implements the type assurance that the types match, gives helpful mismatch message
  let
    inst = val.getTypeInst 
    cncpt = int inst[^1].intval
    idTable = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for i, typ in implTable[cncpt][1..^1]:
    idTable.add:
      nnkOfBranch.newTree(newLit i, newLit fmt"'{val.repr}' is type '{typ[0].repr}' but wanted '{b.repr}'.")
  idTable.add nnkElse.newTree(newLit("Unexpected type ID"))

  result = genast(val, idTable, ofOp = ofImpl, b):
    if not ofOp(val, b):
      raise newException(ImplConvDefect, idTable)

proc `=destroy`[Count, Conc: static int](obj: var ImplObj[Count, Conc]) =
  unrefObj(obj)



{.experimental: "dotOperators".}

macro `.()`*(val: ImplObj, field: untyped, args: varargs[untyped]): untyped =
  ## Implements the logic for UFCS calls so nothing annoying is required to call the procedures
  let
    inst = val.getTypeInst
    (ind, def) = getProcIndexAndDef(val, inst[^1], field)
    pTy = nnkProcTy.newTree()

  if nnkNilLit in {ind.kind, def.kind}:
    let concptName = implTable[int inst[^1].intval][0][0]
    error(fmt"'{field}' proc not found for concept: '{concptName}'.", field)

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
    if isPtrObj:
      genAst():
        ptr UncheckedArray[byte]
    else:
      genAst():
        UncheckedArray[byte]

  let prc = genSym(nskLet, "proc")

  result = newStmtList():
    genast(ind, val, pTy, prc):
      let prc = cast[pTy](val.vtable[ind])

  result.add newCall(prc)
  result[^1].add:
    # If it's a ptrObject dont derefence, otherwise do reference
    if isPtrObj:
      genAst(val):
        val.obj
    else:
      genAst(val):
        val.obj[]

  for arg in args:
    result[^1].add arg

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