## This module implements a simple interface over dynamic dispatched traits.
## It allows one to define the required implementation for a type to match both at runtime and compile time.
## Enabling the writing of code that does not require inheritance, but still has dynamic dispatch.

import pkg/micros/introspection
import std/[macros, genasts, strutils, strformat, typetraits, macrocache]

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
      def[^2].getTypeInst

  result = typImpl.copyNimTree()
  result[0][1][^2] = nnkBracketExpr.newTree(ident"Traitor", trait)

macro emitTupleType*(trait: typed): untyped =
  ## Exported just to get around generic binding issue
  result = nnkTupleConstr.newTree()
  let impl =
    if trait.typekind == ntyDistinct:
      trait.getImpl()
    else:
      trait.getTypeImpl[1].getImpl()
  for def in impl[^1][0]:
    let typImpl = def[^2].getTypeInst
    case typImpl.typeKind
    of ntyProc:
      result.add deAtomProcType(def, trait)
    else:
      for prc in typImpl:
        result.add deAtomProcType(prc, trait)

type
  ValidTraitor* = concept f ## Forces tuples to only have procs that have `Atom` inside first param
    for field in f.distinctBase().fields:
      when field is (proc):
        field.paramTypeAt(0) is Atom
        atomCount(typeof(field)) == 1
      else:
        for child in field.fields:
          child.paramTypeAt(0) is Atom
          atomCount(typeof(child)) == 1
    f.distinctBase() is tuple

  Traitor*[Traits: ValidTraitor] = ref object of RootObj ##
    ## Base Trait object used to ecapsulate the `vtable`
    when defined(traitor.fattraitors):
      vtable*: typeof(emitTupleType(Traits)) # emitTupleType(Traits) # This does not work cause Nim generics really hate fun.
    else:
      vtable*: ptr typeof(emitTupleType(Traits)) # ptr emitTupleType(Traits) # This does not work cause Nim generics really hate fun.

  TypedTraitor*[T; Traits: ValidTraitor] {.final.} = ref object of Traitor[Traits] ##
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
  let procType = origType.getTypeInst[0].copyNimTree
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

  result.params[0] = procType[0]

  for i, def in procType[1..^1]:
    let arg = genSym(nskParam, "param" & $i)
    var theTyp = newStmtList(def[^2].copyNimTree)

    if i == 0:
      theTyp = traitType
      call.add nnkDotExpr.newTree(nnkCall.newTree(typedTrait, arg), ident"data")
    else:
      call.add arg
    result.params.add newIdentDefs(arg, theTyp)

  result[^1] = call
  result = newStmtList(result, result[0])

macro emitPointerProc(trait, instType: typed): untyped =
  result = nnkTupleConstr.newTree()
  let impl = trait.getImpl[^1][0]
  for def in impl:
    let defImpl = def[^2].getTypeInst
    case defImpl.typeKind
    of ntyProc:
      result.add genPointerProc(def[0], def[^2], instType, trait)
    else:
      for prc in defImpl:
        result.add genPointerProc(def[0], prc, instType, trait)

proc genProc(typ, traitType, name: Nimnode, offset: var int): NimNode =
  case typ.typeKind
  of ntyProc:
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
    let
      theCall = newCall(newEmptyNode())
      body = newStmtList()
    var atomParam: NimNode
    for i, def in typ.params[1..^1]:
      let paramName = genSym(nskParam, "param" & $i)
      var theArgTyp = newStmtList(def[^2])

      if i == 0:
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

macro genProcs(trait: Traitor): untyped =
  var tupl = trait.getTypeInst[^1].getTypeImpl()
  if tupl.kind != nnkDistinctTy:
    error("Trait is not a distinct tuple", tupl)
  tupl = tupl[0]

  result = newStmtList()
  var offset = 0
  for field in tupl:
    result.add genProc(field[1], trait.getTypeInst(), field[0], offset)

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

proc format(val: InstInfo): string =
  fmt"{val.filename}({val.line}, {val.column})"

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

  proc toTrait*[T](val: sink T, _: typedesc[trait]): Traitor[trait] =
    when defined(traitor.fattraitors):
      TypedTraitor[T, trait](vtable: static(emitPointerProc(trait, T)), data: ensureMove val)
    else:
      let vtable {.global.} = static(emitPointerProc(trait, T))
      TypedTraitor[T, trait](vtable: vtable.addr, data: ensureMove val)

  {.checks: off.}
  genProcs(default(Traitor[trait]))
  {.checks:on.}

template emitConverter*(T: typedesc, trait: typedesc[ValidTraitor]) =
  ## Emits a converter from `T` to `Traitor[trait]`
  ## This allows skipping of `val.toTrait(trait)`
  converter convToTrait*(val: sink T): Traitor[trait] {.inject.} = val.toTrait trait
