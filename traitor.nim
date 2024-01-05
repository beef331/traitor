import pkg/micros/introspection
import std/[macros, genasts, strutils, strformat]

type Atom* = distinct void ##[
  Default field name to be replaced for all Traits.
  As it derives from void it never can be instantiated.
]##

proc atomCount(p: typedesc[proc]): int =
  for field in default(paramsAsTuple(p(nil))).fields:
    when field is Atom:
      inc result

type
  ValidTraitor* = concept f ## Forces tuples to only have procs that have `Atom` inside first param
    for field in f.fields:
      when field is (proc):
        field.paramTypeAt(0) is Atom
        atomCount(typeof(field)) == 1
      else:
        for child in field.fields:
          child.paramTypeAt(0) is Atom
          atomCount(typeof(child)) == 1
    f is tuple

  Traitor*[Traits: ValidTraitor] = ref object of RootObj
    id*: uint16

  TypedTraitor*[T; Traits: ValidTraitor] {.final.} = ref object of Traitor[Traits]
    data*: T

template typedTo*[T](trait: typedesc[ValidTraitor], _: typedesc[T]): untyped =
  ## Takes in a `trait` and `T` and emits `TypedTraitor[T, trait]`
  TypedTraitor[T, trait]

proc getData*[T; Traits](tratr: Traitor[Traits], _: typedesc[T]): var T =
  ## Converts `tratr` to `TypedTrait[T, Traits]` then access `data`
  TypedTraitor[T, Traits](tratr).data

proc removeAtom(stmt, typ: NimNode): bool =
  for i, node in stmt:
    case node.kind
    of nnkSym:
      if node == bindSym"Atom":
        stmt[i] = typ # No early return other branches might have `Atom`
        result = true
      elif node.symKind == nskParam:
        stmt[i] = ident $node
    else:
      result = result or removeAtom(node, typ)

proc genPointerProc(name, origType, instType, traitType: NimNode): NimNode =
  let procType = origType.getTypeInst[0].copyNimTree
  result = genast():
    proc() {.nimcall.} = discard

  let
    call = newCall(ident name.strVal)
    traitType = nnkBracketExpr.newTree(bindSym"TypedTraitor", instType, traitType)

  if not procType[0].eqIdent"void":
    result.params[0] = procType[0]

  for i, def in procType[1..^1]:
    let
      arg = genSym(nskParam, "param" & $i)
      theTyp = newStmtList(def[^2].copyNimTree)

    if theTyp.removeAtom(traitType):
      call.add nnkDotExpr.newTree(arg, ident"data")
    else:
      call.add arg
    result.params.add newIdentDefs(arg, theTyp)
  let conv = nnkPar.newTree(origType.getTypeInst().copyNimTree)
  discard conv.removeAtom(instType)
  #call[0] = newCall(conv, ident name.strVal)
  result[^1] = call
  result = nnkCast.newTree(bindSym"pointer", result)

macro emitPointerProc(name, prc, typ: typed): untyped =
  let
    procType = prc.getTypeInst()
    trait = prc[0][1]
  result = nnkBracket.newTree()
  case procType.typeKind
  of ntyTuple:
    for theProc in procType:
      result.add genPointerProc(name, theProc, typ, trait)
  else:
    result.add genPointerProc(name, prc, typ, trait)


proc getTupleArity(tupl: NimNode): int =
  for field in tupl:
    case field[1].getType.typeKind
    of ntyProc:
      inc result
    of ntyTuple:
      inc result, field[1].len
    else:
      error("Unexpected AST: ", field)

macro getTraitImpls*(tupl: typedesc): untyped =
  newLit tupl.getTypeImpl[^1].getTypeImpl.getTupleArity()

proc genProc(typ, traitType, name, table: Nimnode, offset: var int, arity: int): NimNode =
  case typ.typeKind
  of ntyProc:
    result = genast(traitType, name = ident $name):
      proc name*() = discard
    if typ.params[0] != void.getType():
      result.params[0] = typ.params[0].copyNimTree
    let
      theCall = newCall(newEmptyNode())
      body = newStmtList()
    for i, def in typ.params[1..^1]:
      let paramName = genSym(nskParam, "param" & $i)
      var theArgTyp = newStmtList(def[^2])
      discard theArgTyp.removeAtom(traitType)

      if i == 0:
        body.add newLetStmt(ident"id", newDotExpr(paramName, ident"id"))

      result.params.add newIdentDefs(paramName, theArgTyp)
      theCall.add paramName
    let toCastType = typ.copyNimTree()
    discard toCastType.removeAtom(traitType)

    theCall[0] = genast(offset, arity, table, toCastType):
      cast[toCastType](table[id * arity + offset])

    result[^1] = newStmtList(body, theCall)

    inc offset

  of ntyTuple:
    result = newStmtList()
    for child in typ:
      result.add genProc(child, traitType, name, table, offset, arity)
  else:
    error("Unexpected type", typ)


macro genProcs(trait: Traitor, table: seq[pointer]): untyped =
  let
    tupl = trait.getTypeInst[^1].getTypeImpl()
    tupleArity = tupl.getTupleArity()
  result = newStmtList()
  var offset = 0
  for field in tupl:
    result.add genProc(field[1], trait.getTypeInst(), field[0], table, offset, tupleArity)

proc pointerProcError(trait: typedesc[ValidTraitor], T: typedesc): string =
  for name, field in default(trait).fieldPairs:
    when field is (proc):
      when not compiles(emitPointerProc(name, field, T)):
        result.add name
        result.add ": "
        result.add $typeof(field)
        result.add "\n"
    else:
      for child in field.fields:
        when not compiles(emitPointerProc(name, child, T)):
          result.add name
          result.add ": "
          result.add $typeof(child)
          result.add "\n"

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
  const info = instantiationInfo(fullpaths = true)
  static:
    const (has, ind) = traitsContain(trait)
    when has:
      doError("Trait named '" & $trait & "' was already implemented at: " & implementedTraits[ind][1].format, info)
    addTrait(trait, instantiationInfo(fullpaths = true))
  var traitVtable: seq[pointer]
  var counter {.compileTime.} = 0u16

  proc toTrait*[T](val: sink T, _: typedesc[trait]): Traitor[trait] =
    var id {.global.} = 0u16
    const errors = pointerProcError(trait, T)

    when false and errors.len > 0:
      doError(
          "'$#' failed to match the trait '$#' it does not implement the following procedure(s):\n$#" %
          [$T, $trait, errors], instantiationInfo(fullpaths = true))
    else:
      for name, field in default(trait).fieldPairs:
        traitVtable.add emitPointerProc(name, field, T)
      id = uint16 traitVtable.high div trait.getTraitImpls()

      TypedTraitor[T, trait](id: id, data: val)


  genProcs(default(Traitor[trait]), traitVtable)

template emitConverter*(T: typedesc, trait: typedesc[ValidTraitor]) =
  ## Emits a converter from `T` to `Traitor[trait]`
  ## This allows skipping of `val.toTrait(trait)`
  converter convToTrait*(val: sink T): Traitor[trait] {.inject.} = val.toTrait trait


when isMainModule:
  type
    MyTrait = tuple[
      doThing: (
        proc(_: Atom) {.nimcall.},
        proc(_: Atom, _: int) {.nimcall.}),
      doOtherThing: proc(_: Atom, _: float){.nimcall.},
      `$`: proc(_: Atom): string {.nimcall.}]
    MyOtherTrait = tuple[
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
