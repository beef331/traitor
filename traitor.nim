import std/[macros, macrocache, strformat, genasts, sugar, algorithm, enumerate, tables]

type 
  ImplConvDefect = object of Defect
  DynamicImplObj[PCount: static int; Conc: static seq[int]] = object
    vTable: array[PCount, pointer]
    idBacker: int # To allow typechecking at runtime
    obj: ptr UncheckedArray[byte]
  FixedImplObj[PCount, BuffSize: static int; Conc: static seq[int]] = object
    vTable: array[PCount, pointer]
    idBacker: int # To allow typechecking at runtime
    obj: array[BuffSize, byte]

  ImplObj = DynamicImplObj or FixedImplObj

  ConceptImpl = enum
    getTypeName, getTypeImpl

proc id*(impl: ImplObj): int = impl.idBacker


var implTable {.compileTime.} = CacheSeq"ConceptImplTable"
const traitorBufferSize {.intdefine.}: int = -1
var currentBuffSize {.compileTime.} = traitorBufferSize

template withImplementBufferSize*(tempSize: int, body: untyped) =
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
        if x[0][0] == typ[ids.len]:
          ids.add ind
          break search
      error(fmt"Cannot find {typ[ids.len].repr}, it is not be subscribed with 'implements'.", typ[ids.len])
  ids.sort
  for id in ids:
    result.add newLit id

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

iterator `[]`(n: NimNode, slice: HSlice[int, BackwardsIndex]): NimNode =
  for i in slice.a .. n.len - int(slice.b):
    yield n[i]


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
  ## Yields Concept names from ids
  for concpt in concepts:
    yield implTable[concpt][0][0]

iterator conceptNames(concepts: NimNode): NimNode =
  ## Yields the symbols of the concepts from bracketexpr of int ids
  assert concepts.kind == nnkBracket
  let concepts = collect(for x in concepts: int x.intval)
  for concpt in conceptNames concepts:
    yield concpt

iterator conceptProcs(typ, concepts: NimNode): NimNode =
  ## returns `id`, `procName` for the given `typ`
  assert concepts.kind == nnkBracket
  let concepts = collect(for x in concepts: int x.intVal)
  var yieldedProcs = initTable[string, seq[NimNode]]() # Only want to yield an impl once

  proc didYield(prc: NimNode): bool =
    # Checks if this proc has been yielded if not adds it to the yield table
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
      newProc.replaceSelf(theType) # Replace "a: Self"
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
      if iProc.sameProc pDef: # If we hit a same proc add it
        var
          fullyImplemented = 0 # Count how many procedures are implemented
          implementedNewProc = false # If this ticked a implementation over
        for impl in typImpl:
          if impl.kind == nnkPar: # Due to storing `(sym, proc)` inside the impl table
            if impl[1].sameProc(pDef) and impl[0].kind == nnkEmpty:
              impl[0] = pDef[0] # Bind the name to the pdef we're adding, so we can use it later
              implementedNewProc = true
            if impl[0].kind == nnkSym: # We hit something already implemented
              inc fullyImplemented
        return (fullyImplemented == typImpl.len - 1 and implementedNewProc, typImpl[0])


proc getProcs(val, cncpt: NimNode): seq[NimNode] =
  ## Get all proc names for this concept for the type
  for prc in conceptProcs(val.getTypeInst, cncpt):
    result.add prc

proc getProcs(concepts: openArray[int]): seq[NimNode] =
  ## Get all the proc names for this concept
  for concpt in concepts:
    for prc in implTable[concpt][0][1]:
      result.add prc[0]

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
          if x[0].kind != nnkSym: # If the the sym slot is empty it's an unimplemented proc
            let impl = nnkProcDef.newTree
            x[1].copyChildrenTo(impl)
            localMissings.add impl.repr
            localMissings.add "\n"
        if localMissings.len > 0:
          allMissings.add fmt("\nMissing impls for type: '{impl[0]}', to match '{concpts[0][0]}':\n{localMissings}")
  if allMissings.len > 0:
    error(allMissings)

macro implObj*(concepts: varargs[typed]): untyped =
  ## Generates a type for the object from concepts,
  ## useful for making typedescs
  let
    ids = collect:(for x in toId(concepts): int x.intval)
    procs = getProcs(ids)

  result = genAst(ids, pcount = procs.len, currentBuffSize):
    when currentBuffSize > 0:
      FixedImplObj[pcount, currentBuffSize, ids]
    else:
      DynamicImplObj[pcount, ids]


macro impl*(pDef: typed): untyped =
  ## Adds `pdef` to `implTable` for all concepts that require it
  ## emits a converter if fully matched.
  ## Works on blocks of procedures and also as a pragma.
  let pDefs =
    if pDef.kind == nnkProcDef:
      newStmtList(pDef)
    else:
      pDef
  result = newStmtList(pDef)
  for pDef in pdefs:
    if pdef.kind != nnkProcDef:
      error("Cannot implement a non procedure.", pdef)
    var implementsOnce = false
    for concpt in implTable:
      let (fullyImpls, typ) = markIfImpls(pDef, concpt)
      if pDef.kind != nnkEmpty:
        implementsOnce = true
      if fullyImpls:
        let
          conceptName = concpt[0][0]
          name = ident "to" & $conceptName
        result.add:
          genASt(name, typ, conceptName):
            converter name*(obj: typ): implObj(conceptName) = obj.toImpl(conceptName)
    if not implementsOnce:
      error("Attempting to implement unknown proc.", pDef)

macro toImpl*(val: typed, constraint: varargs[typed]): untyped =
  ## Converts an object to the desired interface
  let
    conceptIds = constraint.toId()
    procs = getProcs(val, conceptIds)
    rawProcs = nnkBracket.newTree()
    typeId = val.getTypeId(conceptIds)
  if typeId < 0:
    error(fmt"Cannot to convert '{val.getType.repr}' to {constraint.repr}.", val)

  for x in procs:
    # Procs are pointers but are non homogenous so cast them to be homgoenous
    rawProcs.add nnkCast.newTree(ident"pointer", x)

  let neededSize = val.getType.getSize
  if neededSize > currentBuffSize and currentBuffSize > 0:
    error(fmt"Attempting to use a fixed array of {currentBuffSize}, but need atleast {neededSize} for type {val.getTypeInst.repr}", val)

  result = genAst(rawProcs, pCount = procs.len, val, conceptIds, typeId, currentBuffSize):
    when currentBuffSize > 0:
      var
        data {.noInit.}: array[currentBuffSize, byte]
        obj = val # So we support `MyObj(a: 100).toImpl(SomeConcept)`
      when val is ref:
        GC_Ref(val) # So ref types behave properly
      copyMem(data[0].addr, obj.unsafeAddr, sizeof(val))
      FixedImplObj[pCount, currentBuffSize, @conceptIds](vtable: rawProcs, idBacker: typeId, obj: data)
    else:
      var
        data  = cast[ptr UncheckedArray[byte]](createU(byte, sizeof(val)))
        obj = val # So we support `MyObj(a: 100).toImpl(SomeConcept)`
      when val is ref:
        GC_Ref(val) # So ref types behave properly
      copyMem(data[0].addr, obj.unsafeAddr, sizeof(val))
      DynamicImplObj[pCount, @conceptIds](vtable: rawProcs, idBacker: typeId, obj: data)

macro ofImpl(val: ImplObj, b: typedesc): untyped =
  ## Does the internal logic for the `of` operator, checking if the id's match the desired type
  let
    inst = val.getTypeInst 
    concepts = inst[^1]
  var ind = 0
  for (id, typ) in conceptImpls(concepts):
    # Searches for the type ID, breaking when found
    if typ == b:
      ind = id
      break

  result = genast(val, ind):
    val.id == ind

macro emitConverters*(concepts: varargs[typed]): untyped =
  ## Generates converters for each type passed
  result = newStmtList()
  for concpt in concepts:
    let 
      typCall = nnkCall.newTree(bindsym"implObj")
      valName = ident"val"
      toImplCall = newCall(bindSym"toImpl", valName)

    case concpt.kind
    of nnkSym:
      typCall.add concpt
      toImplCall.add concpt
    of nnkBracket:
      for i, typ in concpt:
        typCall.add typ
        toImplCall.add typ

    else: discard
    result.add:
      genAst(typCall, toImplCall, valName, name = genSym(nskConverter, "toImplObj")):
        converter name[T](valName: T): typCall = toImplCall

macro unrefObj(val: ImplObj): untyped =
  ## Unref's the object and destroys the object that it wraps
  let
    inst = val.getTypeInst
    concepts = collect:(for x in inst[^1]: int x.intVal)
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for (id, name) in conceptImpls(concepts):
    # id is the `typeId` and needed for knowing the underlying type
    result.add:
      nnkOfBranch.newTree(newLit id):
        genAst(val, typ = name):
          when val is FixedImplObj:
            when typ is ref:
              GC_UnRef(cast[ptr typ](val.obj.addr)[]) # Try not to leak GC'd memory
            `=destroy`(cast[ptr typ](val.obj.addr)[]) # Custom destructors should work
          else:
            when typ is ref:
              GC_UnRef(cast[ptr typ](val.obj)[]) # Try not to leak GC'd memory
            `=destroy`(cast[ptr typ](val.obj)[]) # Custom destructors should work

  result.add nnkElse.newTree(nnkDiscardstmt.newTree(newEmptyNode()))

macro ensureType(val: ImplObj, b: typedesc): untyped =
  ## Implements the type assurance that the types match, gives helpful mismatch message
  let
    inst = val.getTypeInst 
    concepts = collect(for x in inst[^1]: int x.intval)
    idTable = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  # Makes a case statement for figuring out the actual type and storing the good message
  for (id, typ) in conceptImpls(concepts):
    idTable.add:
      nnkOfBranch.newTree(newLit id, newLit fmt"'{val.repr}' is type '{typ.repr}' but wanted '{b.repr}'.")
  idTable.add nnkElse.newTree(newLit("Unexpected type ID"))

  result = genast(val, idTable, ofOp = ofImpl, b):
    if not ofOp(val, b): # Probably should only be enabled for debug/release?
      raise newException(ImplConvDefect, idTable)

macro isPtr(val: ImplObj): untyped =
  ## Figures out if the type is a `ptr` or `ref` to enable proper semantics
  
  let
    inst = val.getTypeInst 
    concepts = collect(for x in inst[^1]: int x.intval)
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(val, ident"id"))
  for (id, typ) in conceptImpls(concepts):
    # Case statement emits `of id: typ is (ref or ptr)`
    result.add:
      nnkOfBranch.newTree(newLit id):
        genast(val, typ):
          typ is (ref or ptr)
  result.add nnkElse.newTree(newLit true)

proc `=destroy`[Count: static int; Conc: static seq[int]](obj: var DynamicImplObj[Count, Conc]) =
  unrefObj(obj)
  dealloc(obj.obj)

proc `=destroy`[Count, Size: static int; Conc: static seq[int]](obj: var FixedImplObj[Count, Size, Conc]) =
  unrefObj(obj)

{.experimental: "dotOperators".}

macro `.()`*(val: ImplObj, field: untyped, args: varargs[untyped]): untyped =
  ## Implements the logic for UFCS calls so nothing annoying is required to call the procedures
  let
    inst = val.getTypeInst
    (ind, def) = getProcIndexAndDef(val, inst[^1], field)
    pTy = nnkProcTy.newTree()
  if nnkNilLit in {ind.kind, def.kind}: # Should be nil on error
    let mismatch = block: # Make a purdy error message, people love those I hear
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
    isPtrObj = def[3][1][^2].typeKind == ntyVar # might need to add more later

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
  pTy[0][1][^2] = # Replace paramter with pointer, seems to work but I have a feeling, small objects will fail
    genAst():
      pointer


  let prc = genSym(nskLet, $field) # nice name for proc incase of errors

  result = newStmtList():
    genast(ind, val, pTy, prc):
      let prc = cast[pTy](val.vtable[ind]) # cast proc to our original type but with `pointer` as first arg

  result.add newCall(prc)

  result[^1].add:
    # Handle first parameter our object
    if isPtrObj:
      genAst(val):
        when val is FixedImplObj:
          cast[pointer](val.obj.addr)
        else:
          val.obj
    else:
      genAst(val):
        when val is FixedImplObj:
          cast[pointer](val.obj.addr)
        else:
          if isPtr(val):
            let pntr = cast[ptr UncheckedArray[int]](val.obj)[0]
            cast[pointer](pntr)
          else:
            cast[pointer](val.obj)

  for arg in args: # Add remaining args
    result[^1].add arg


template `of`*(implObj: ImplObj, T: typedesc): bool =
  ## Returns true if the `implObj` is really a `T`
  ofImpl(implObj, T)

template `as`*(implObj: ImplObj, T: typedesc[not ImplObj]): untyped =
  ## Converts `implObj` to `T` raising a defect if it's not.
  ensureType(implObj, T)
  when implObj is FixedImplObj:
    when T is ref:
      let val = cast[ptr T](implObj.obj.addr)[]
      Gc_Ref(val) # Needed since we're instantiating from a cast
      val
    else:
      cast[ptr T](implObj.obj.addr)[]
  else:
    when T is ref:
      let val = cast[ptr T](implObj.obj)[]
      Gc_Ref(val) # Needed since we're instantiating from a cast
      val
    else:
      cast[ptr T](implObj.obj)[]

template to*(implObj: ImplObj, T: typedesc[not ImplObj]): untyped =
  ## Alias of `as` used for easier chaining on conversion(accessing fields and the like.)
  implObj as T