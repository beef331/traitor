## This module implements a simple interface over dynamic dispatched traits.
## It allows one to define the required implementation for a type to match both at runtime and compile time.
## Enabling the writing of code that does not require inheritance, but still has dynamic dispatch.


## Defining `-d:traitor.fattraitors` allows one to change where the vtable is stored.
## By default there is a vtable generated per trait.
## This flag moves the the vtable to the `Traitor` object which increases memory usage,
## but in limited testing can improve dispatch time through cache optimising.

## Defining `-d:traitor.nicenames` can be used to make the generate procedures have nicer names for debugging.


import pkg/micros/introspection
import std/[macros, genasts, strutils, strformat, typetraits, macrocache]

proc replaceType(tree, arg, inst: NimNode) =
  for i, node in tree:
    if node.eqIdent arg:
      tree[i] = inst
    else:
      replaceType(node, arg, inst)

proc instGenTree(trait: NimNode): NimNode =
  let trait =
    case trait.typeKind
    of ntyGenericInst, ntyDistinct, ntyGenericBody:
      trait
    else:
      trait.getTypeInst()[1]

  case trait.kind
  of nnkSym:
    trait.getImpl()[^1][0]
  of nnkBracketExpr:
    let trait =
      if trait.typeKind == ntyTypeDesc:
        trait[1]
      else:
        trait

    let
      typImpl = trait[0].getImpl()
      genParams = typImpl[1]
      tree = typImpl[^1].copyNimTree()
    for i, param in genParams:
      tree.replaceType(param, trait[i + 1])
    tree[0] # Skip distinct
  else:
    trait

macro isGeneric*(t: typedesc): untyped =
  let t =
    if t.kind == nnkBracketExpr:
      t[0]
    else:
      t
  #newLit t.getTypeImpl[1].getImpl[1].kind == nnkGenericParams
  newLit true

type Atom* = distinct void ##
  ## Default field name to be replaced for all Traits.
  ## As it derives from void it never can be instantiated.

proc atomCount(p: typedesc[proc]): int =
  {.warning[UnsafeDefault]: off.}
  for field in default(paramsAsTuple(p(nil))).fields:
    when field is Atom:
      inc result
  {.warning[UnsafeDefault]: on.}

proc deAtomProcType(def, trait: NimNode): NimNode =
  let typImpl =
    if def.kind == nnkProcTy:
      def
    else:
      def[^2]

  result = typImpl.copyNimTree()
  result[0][1][^2] = nnkBracketExpr.newTree(ident"Traitor", trait)

macro emitTupleType*(trait: typedesc): untyped =
  ## Exported just to get around generic binding issue
  result = nnkTupleConstr.newTree()
  let impl = trait.instGenTree()
  let trait = trait.getTypeInst[1]
  for def in impl:
    case def[^2].typeKind
    of ntyProc:
      result.add deAtomProcType(def, trait)
    else:
      for prc in def[^2]:
        result.add deAtomProcType(prc, trait)

type
  GenericType* = concept type F ## Cannot instantiate it so it's just checked it's a `type T[...] = distinct tuple`
    isGeneric(F)

  TraitType* = concept f ## Forces tuples to only have procs that have `Atom` inside first param
    for field in f.distinctBase().fields:
      when field is (proc):
        field.paramTypeAt(0) is Atom
        atomCount(typeof(field)) == 1
      else:
        for child in field.fields:
          child.paramTypeAt(0) is Atom
          atomCount(typeof(child)) == 1
    f.distinctBase() is tuple

  ValidTraitor* = GenericType or TraitType

  Traitor*[Traits: ValidTraitor] = ref object of RootObj ##
    ## Base Trait object used to ecapsulate the `vtable`
    vtable*: typeof(emitTupleType(typeof(Traits)))

  TypedTraitor*[T; Traits: ValidTraitor] {.final, acyclic.} = ref object of Traitor[Traits] ##
    ## Typed Trait object has a known data type and can be unpacked
    data*: T

  StaticTraitor*[Traits: ValidTraitor] = concept st ## Allows generic dispatch on types that fit traits
    st.toTrait(Traits) is Traitor[Traits]

  AnyTraitor*[Traits: ValidTraitor] = StaticTraitor[Traits] or Traitor[Traits] ## Allows writing a procedure that operates on both static and runtime.

  InstInfo = typeof(instantiationInfo())

proc getData*[T; Traits](tratr: Traitor[Traits], _: typedesc[T]): var T =
  ## Converts `tratr` to `TypedTrait[T, Traits]` then access `data`
  runnableExamples:
    type
      MyTrait = distinct tuple[doThing: proc(_: Atom){.nimcall.}]
      MyType = object
        x: int
    implTrait MyTrait
    proc doThing(typ: MyType) = discard
    let traitObj = MyType(x: 100).toTrait MyTrait
    assert traitObj.getData(MyType) == TypedTraitor[MyType, MyTrait](traitObj).data


  TypedTraitor[T, Traits](tratr).data

proc genPointerProc(name, origType, instType, origTraitType: NimNode): NimNode =
  let procType = origType[0].copyNimTree

  when defined(traitor.nicenames):
    result = genast(name = ident $name & instType.getTypeImpl[1].repr.multiReplace({"[" : "_", "]": ""})):
      proc name() {.nimcall.} = discard
  else:
    result = genast(name = gensym(nskProc, $name)):
      proc name() {.nimcall, gensym.} = discard

  let
    call = newCall(name)
    traitType = nnkBracketExpr.newTree(bindSym"Traitor", origTraitType)
    typedTrait = nnkBracketExpr.newTree(bindSym"TypedTraitor", instType, origTraitType)

  result.params[0] = origType[0][0]

  for def in procType[1..^1]:
    for _ in def[0..^3]:
      let arg = genSym(nskParam, "param" & $(result.params.len - 1))
      var theTyp = def[^2].copyNimTree

      if result.params.len - 1 == 0:
        theTyp = traitType
        call.add nnkDotExpr.newTree(nnkCall.newTree(typedTrait, arg), ident"data")
      else:
        call.add arg
      result.params.add newIdentDefs(arg, theTyp)

  result[^1] = call
  result = newStmtList(result, result[0])

macro emitPointerProc(trait, instType: typed, err: static bool = false): untyped =
  let trait = trait.getTypeInst[^1]
  result =
    if err:
      nnkBracket.newTree()
    else:
      nnkTupleConstr.newTree()
  let impl = trait.instGenTree()
  if err:
    for def in impl:
      let defImpl = def[^2].getTypeInst
      case defImpl.typeKind
      of ntyProc:
        let prc = genPointerProc(def[0], def[^2], instType, trait)
        result.add:
          genast(prc, typ = def[^2]):
            when not compiles(prc):
              astToStr(typ)
            else:
              ""
      else:
        for prc in defImpl:
          let genProc = genPointerProc(def[0], prc, instType, trait)
          result.add:
            genast(genProc, prc):
              when not compiles(genProc):
                astToStr(prc)
              else:
                ""
  else:
    for def in impl:
      let defImpl = def[^2].getTypeInst
      case defImpl.typeKind
      of ntyProc:
        result.add genPointerProc(def[0], def[^2], instType, trait)
      else:
        for prc in defImpl:
          result.add genPointerProc(def[0], prc, instType, trait)

proc desym(tree: NimNode) =
  for i, node in tree:
    if node.kind == nnkSym:
      tree[i] = ident $node
    else:
      desym node

proc genProc(typ, traitType, name: Nimnode, offset: var int): NimNode =
  case typ.typeKind
  of ntyProc:
    let traitType = traitType.copyNimTree()
    when defined(traitor.nicenames):
      result = genast(
        name = ident $name,
        exportedName = newLit $name & "_" & traitType.repr.multiReplace({"[": "_", "]": ""})
      ):
        proc name*() {.exportc: exportedName.} = discard
    else:
      result = genast(name = ident $name):
        proc name*() = discard
    result.params[0] = typ.params[0].copyNimTree

    let genParams = traitType[1].getImpl()[1]
    if genParams.len > 0:
      result[2] = nnkGenericParams.newNimNode()
      let genericTrait = nnkBracketExpr.newTree(traitType[1])
      traitType[1] = genSym(nskType, "Arg")
      for typ in genParams:
        result[2].add newIdentDefs(ident($typ), newEmptyNode())
        genericTrait.add ident($typ)
      result[2].add newIdentDefs(traitType[1], genericTrait)

    let
      theCall = newCall(newEmptyNode())
      body = newStmtList()
    var atomParam: NimNode
    for i, def in typ.params[1..^1]:
      for _ in def[0..^3]:
        let paramName = genSym(nskParam, "param" & $(result.params.len - 1))
        var theArgTyp = newStmtList(def[^2])

        if result.params.len - 1 == 0:
          atomParam = paramName
          theArgTyp = traitType

        result.params.add newIdentDefs(paramName, theArgTyp)
        theCall.add paramName

    theCall[0] = genast(offset, atomParam):
      atomParam.vtable[offset]

    result[^1] = newStmtList(body, theCall)

    inc offset

  of ntyTuple:
    result = newStmtList()
    for child in typ:
      result.add genProc(child, traitType, name, offset)
  else:
    error("Unexpected type", typ)

macro genProcs(origTrait: typedesc): untyped =
  let trait = origTrait[^1]
  var tupl = trait.getTypeInst[^1].getTypeImpl()
  if tupl.kind != nnkDistinctTy:
    error("Trait is not a distinct tuple", tupl)
  tupl = trait.instGenTree()

  result = newStmtList()
  var offset = 0
  for field in tupl:
    result.add genProc(field[1], origTrait, field[0], offset)

macro doError(msg: static string, info: static InstInfo) =
  let node = newStmtList()
  node.setLineInfo(LineInfo(fileName: info.filename, line: info.line, column: info.column))
  error(msg, node)

var implementedTraits {.compileTime.}: seq[(NimNode, InstInfo)]

macro addTrait(t: typedesc, info: static InstInfo) =
  if t.kind != nnkSym:
    error("Did not use a type alias for the trait tuple.", t)
  implementedTraits.add (t, info)

macro traitsContain(typ: typedesc): untyped =
  result = newLit((false, -1))
  for i, x in implementedTraits:
    if x[0] == typ:
      return newLit((true, i))

macro genbodyCheck(t: typedesc, info: static InstInfo): untyped =
  if t.getTypeInst[1].typeKind == ntyGenericBody:
    let node = newStmtList()
    node.setLineInfo(LineInfo(fileName: info.filename, line: info.line, column: info.column))
    error("Cannot use `toTrait` due to lacking generic parameters on '" & t.getTypeInst[1].repr & "'", node)

proc format(val: InstInfo): string =
  fmt"{val.filename}({val.line}, {val.column})"

const errorMessage = "'$#' failed to match '$#' due to missing the following procedure(s):\n"

template implTrait*(trait: typedesc[ValidTraitor]) =
  ## Emits the `vtable` for the given `trait` and a procedure for types to convert to `trait`.
  ## It is checked that `trait` is only implemented once so repeated calls error.
  runnableExamples:
    type MyTrait = distinct tuple[bleh: proc(_: Atom, _: int) {.nimcall.}]
    implTrait MyTrait
  const info {.used.} = instantiationInfo(fullpaths = true)
  static:
    const (has, ind {.used.}) = traitsContain(trait)
    when has:
      doError("Trait named '" & $trait & "' was already implemented at: " & implementedTraits[ind][1].format, info)
    addTrait(trait, instantiationInfo(fullpaths = true))

  proc errorCheck[T](traitType: typedesc[trait]): string =
    const missing = emitPointerProc(traitType, T, true)
    for i, miss in missing:
      if miss != "":
        if result.len == 0:
          result = errorMessage % [$T, $traitType]
        result.add miss
        if i < missing.high:
          result.add "\n"

  proc toTrait*[T; Constraint: trait](val: sink T, traitTyp: typedesc[Constraint]): auto =
    const procInfo = instantiationInfo(fullPaths = true)
    genbodyCheck(traitTyp, procInfo)
    const missMsg = errorCheck[T](traitTyp)
    when missMsg.len > 0:
      doError(missMsg, instantiationInfo(fullPaths = true))
    else:
      Traitor[traitTyp](TypedTraitor[T, traitTyp](vtable: static(emitPointerProc(traitTyp, T)), data: ensureMove val))

  {.checks: off.}
  genProcs(Traitor[trait])
  {.checks:on.}

template emitConverter*(T: typedesc, trait: typedesc[ValidTraitor]) =
  ## Emits a converter from `T` to `Traitor[trait]`
  ## This allows skipping of `val.toTrait(trait)`
  converter convToTrait*(val: sink T): Traitor[trait] {.inject.} = val.toTrait trait

when defined(nimdoc):
  import traitor/streams
