import std/[macros, macrocache, strformat, genasts, sugar, algorithm, enumerate, tables]

type 
  ImplConvDefect = object of Defect
  DynamicImplObj[Conc: static seq[int]] = object
    idBacker: int # To allow typechecking at runtime
    obj: ptr UncheckedArray[byte]
  FixedImplObj[BuffSize: static int; Conc: static seq[int]] = object
    idBacker: int # To allow typechecking at runtime
    obj: array[BuffSize, byte]

  ImplObj = DynamicImplObj or FixedImplObj

  ConceptImpl = enum
    getTypeName, getTypeImpl

proc id*(impl: ImplObj): int = impl.idBacker


var implTable {.compileTime.} = CacheSeq"ConceptImplTable"
const traitorBufferSize {.intdefine.}: int = -1
var currentBuffSize {.compileTime.} = traitorBufferSize

template withTraitorBufferSize*(tempSize: int, body: untyped) =
  let curr = static: currentBuffSize
  static:
    currentBuffSize = tempSize
  body
  static:
    currentBuffSize = curr


proc toId(typ: NimNode): NimNode =
  ## Converts symbols to their ID, could use a table,
  ## but wouldnt allow same name interfaces.
  result = nnkBracket.newTree()
  let typ =
    if typ.kind == nnkSym:
      nnkBracket.newTree(typ)
    else:
      typ
  var ids: seq[int]
  for i in 0..<typ.len:
    block search:
      for ind, x in enumerate implTable:
        if x[0] == typ[ids.len]:
          ids.add ind
          break search
      error(fmt"Cannot find {typ[ids.len].repr}, it is not be subscribed with 'implements'.", typ[ids.len])
  ids.sort
  for id in ids:
    result.add newLit id

proc getConceptProcs(concpt: NimNode): NimNode = concpt.getImpl[^1][^1]

proc getVtable(concpt: NimNode): NimNode =
  for impl in implTable:
    if impl[0] == concpt:
      return impl[1]

proc maybeCreateTable(concepts: NimNode): NimNode =
  result = newStmtList()
  for concpt in concepts:
    let tab = getVtable(concpt)
    if tab.kind == nnkNilLit:
      let table = genSym(nskVar, $concpt & "Vtable")
      implTable.add newStmtList(concpt, table) # Table stores (concept, tableName, type)
      result.add: 
        genAst(table):
          var table: seq[pointer]

proc getImplType(pdef: NimNode): NimNode =
  result = pdef.params[1][^2]
  if result.kind == nnkVarTy:
    result = result[0]

proc addTypeToTable(typ, concepts: NimNode) =
  for concpt in concepts:
    for impl in implTable:
      if impl[0] == concpt:
        for oldTyp in impl[2..^1]:
          if typ == oldTyp[0]:
            return
        impl.add newStmtList(typ)
        impl[^1].add newSeq[NimNode](concpt.getConceptProcs.len)

proc sameParams(a, b: NimNode): bool =
  ## Checks if the parameters match types including `var/ptr/ref`
  result = a.len == b.len
  if result:
    result = a[^2] == b[^2]
    if not result:
      if a[^2].kind in {nnkRefTy, nnkVarTy, nnkPtrTy}:
        if a[^2][0].eqIdent"Self":
          result = true
        elif a[^2].kind == b[^2].kind:
          result = a[^2][0].sameType(b[^2][0])
      elif a[^2].eqIdent"Self":
        result = true
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


iterator conceptImpls(concepts: NimNode): (NimNode, NimNode) =
  for concpt in concepts:
    for impl in implTable:
      if impl[0] == concpt:
        yield (concpt, impl)

proc implementProc(typ, prc, concepts: NimNode): NimNode =
  result = newStmtList()
  for (concpt, impl) in concepts.conceptImpls:
    for typId, oldTyp in impl[2..^1]:
      if typ == oldTyp[0]:
        for oldPrc in oldTyp[1]:
          if prc.sameProc(oldPrc):
            error("Attempting to reimplement proc", prc)
        let
          concptProcs = concpt.getConceptProcs
          vTable = getVtable(concpt)
        for i, concptProc in concptProcs:
          if sameProc(concptProc, prc):
            oldTyp[i + 1] = prc[0]
            result.add:
              genAst(pName = prc[0], vTable, typId, procCount = concptProcs.len, i):
                if vTable.len <= typId * procCount + i:
                  vTable.setLen(typId * procCount + procCount)
                vTable[typId * procCount + i] = pName


proc ensureFullyImplemented(concepts: NimNode) =
  var missingImpls = ""
  for (concpt, impl) in concepts.conceptImpls:
    let procs = concpt.getConceptProcs
    for typImpl in impl[2..^1]:
      for i, prc in typImpl[1..^1]:
        if prc.kind == nnkNilLit:
          missingImpls.add &"{procs[i].repr} is missing for '{typImpl[0].repr}'\n"
  if missingImpls.len > 0:
    error(&"Missing implementations:\n{missingImpls}")


macro emitConverters*(concepts: varargs[typed]): untyped =
  result = newStmtList()
  for concpt in concepts:
    result.add:
      genAst(concpt, ids = concpt.toId, convName = genSym(nskConverter, "toImplObj")):
        converter convName*[T](val: T): DynamicImplObj[@ids] = val.toImpl(concpt)
  echo result.repr

macro implTraits*(concepts: varargs[typed], pdefs: typed): untyped =
  result = newStmtList(maybeCreateTable(concepts))
  for pdef in pdefs:
    if pdef.kind != nnkProcDef:
      error("Can only work with proc types", pdef)
    let
      theType = pdef.getImplType
      cleanProc = pdef.copyNimTree
    cleanProc[^1] = newEmptyNode()
    cleanProc[^2] = newEmptyNode()
    theType.addTypeToTable(concepts)
    result.add pdef
    result.add theType.implementProc(cleanProc, concepts)
  ensureFullyImplemented(concepts)

macro toImpl*(val: typed, concepts: varargs[typed]) =
