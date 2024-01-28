import pkg/micros/introspection
import std/[macros, genasts, strutils, strformat, typetraits, macrocache]

type Atom* = distinct void ##[
  Default field name to be replaced for all Traits.
  As it derives from void it never can be instantiated.
]##

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

macro emitTupleType(trait: typed): untyped =
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

template indirectIt(desc: typedesc): untyped = typeof(default(desc).typeof().emitTupleType())

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

  Traitor*[Traits: ValidTraitor] = ref object of RootObj
    vtable*: ptr indirectIt(Traits) # ptr emitTupleType(Traits) # This does not work cause Nim generics really hate fun.

  TypedTraitor*[T; Traits: ValidTraitor] {.final.} = ref object of Traitor[Traits]
    data*: T

  StaticTraitor*[Traits: ValidTraitor] = concept st ## Allows generic dispatch on types that fit traits
    st.toTrait(Traits) is Traitor[Traits]

  AnyTraitor*[Traits: ValidTraitor] = StaticTraitor[Traits] or Traitor[Traits] ## Allows writing a procedure that operates on both static and runtime.

proc getData*[T; Traits](tratr: Traitor[Traits], _: typedesc[T]): var T =
  ## Converts `tratr` to `TypedTrait[T, Traits]` then access `data`
  TypedTraitor[T, Traits](tratr).data

proc genPointerProc(name, origType, instType, origTraitType: NimNode): NimNode =
  let procType = origType.getTypeInst[0].copyNimTree
  result = genast():
    proc() {.nimcall.} = discard

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
    result = genast(traitType, name = ident $name):
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

macro doError(msg: static string, info: static typeof(instantiationInfo())) =
  let node = newStmtList()
  node.setLineInfo(LineInfo(fileName: info.filename, line: info.line, column: info.column))
  error(msg, node)

var implementedTraits {.compileTime.}: seq[(NimNode, typeof(instantiationInfo()))]

macro addTrait(t: typedesc, info: static typeof(instantiationInfo())) =
  if t.kind != nnkSym:
    error("Did not use a type alias for the trait tuple.", t)
  implementedTraits.add (t, info)

macro traitsContain(typ: typedesc): untyped =
  result = newLit((false, -1))
  for i, x in implementedTraits:
    if x[0] == typ:
      return newLit((true, i))

proc format(val: typeof(instantiationInfo())): string =
  fmt"{val.filename}({val.line}, {val.column})"

template implTrait*(trait: typedesc[ValidTraitor]) =
  ## Emits the `vtable` for the given `trait` and a procedure for types to convert to `trait`.
  ## It is checked that `trait` is only implemented once so repeated calls error.
  const info {.used.} = instantiationInfo(fullpaths = true)
  static:
    const (has, ind {.used.}) = traitsContain(trait)
    when has:
      doError("Trait named '" & $trait & "' was already implemented at: " & implementedTraits[ind][1].format, info)
    addTrait(trait, instantiationInfo(fullpaths = true))

  proc toTrait*[T](val: sink T, _: typedesc[trait]): Traitor[trait] =
    let vtable {.global.} = static: emitPointerProc(trait, T)
    TypedTraitor[T, trait](vtable: vtable.addr, data: ensureMove val)

  genProcs(default(Traitor[trait]))

template emitConverter*(T: typedesc, trait: typedesc[ValidTraitor]) =
  ## Emits a converter from `T` to `Traitor[trait]`
  ## This allows skipping of `val.toTrait(trait)`
  converter convToTrait*(val: sink T): Traitor[trait] {.inject.} = val.toTrait trait


when isMainModule:
  type
    MyTrait = distinct tuple[
      doThing: (
        proc(_: Atom) {.nimcall.},
        proc(_: Atom, _: int) {.nimcall.}),
      doOtherThing: proc(_: Atom, _: float){.nimcall.},
      `$`: proc(_: Atom): string {.nimcall.}]
    MyOtherTrait = distinct tuple[
      doThing: proc(_: var Atom) {.nimcall.},
      doOtherThing: proc(_: Atom, _: string){.nimcall.}]

  implTrait MyTrait
  implTrait MyOtherTrait

  proc doThing(i: int) = echo i * 30
  proc doThing(i: var int) = inc i
  proc doThing(i, j: int) = echo (i: i, j: j)
  proc doOtherThing(a: int, b: float) = echo a + int(b)
  proc doOtherThing(a: int, b: string) = echo b, ": ", a

  emitConverter int, MyTrait
  emitConverter int, MyOtherTrait


  var a: Traitor[MyTrait] = 100
  echo a
  a.doThing()
  a.doThing(3)
  a.doOtherThing(float 3d)

  proc doThing(f: float) = echo f * 3
  proc doThing(f: var float) = f *= f
  proc doThing(f: float, i: int) = echo (f: f, i: i)
  proc doOtherThing(a, b: float) = echo a * b
  proc doOtherThing(a: float, b: string) = echo b, ": ", a

  emitConverter float, MyTrait
  emitConverter float, MyOtherTrait

  a = 3d

  echo a
  a.doThing()
  a.doThing(3)
  a.doOtherThing(3d)

  var b = 30.toTrait MyOtherTrait
  b.doThing()
  b.doOtherThing("int")
  b = 3d.toTrait MyOtherTrait

  b.doThing()
  b.doOtherThing("float")

  type MyType = object
    x, y: int

  proc `=destroy`(typ: MyType) = echo "Buh bye"

  proc doThing(typ: MyType) = echo (typ.x + typ.y) * 30
  proc doThing(typ: var MyType) = typ.x += typ.y
  proc doThing(typ: MyType, b: int) = echo (typ.x + typ.y) * b
  proc doOtherThing(typ: MyType, b: float) = echo typ.x + int(b)
  proc doOtherThing(typ: MyType, b: string) = echo b, ": ", typ.y

  a = MyType(x: 20, y: 1).toTrait MyTrait
  a.doThing()
  a.doOtherThing(3d)
  echo a

  b = MyType(x: 20, y: 1).toTrait MyOtherTrait
  b.doThing()
  b.doOtherThing("My own Type!")
