import pkg/micros/introspection
import std/[macros, genasts]

type Atom* = distinct void

proc atomCount(p: typedesc[proc]): int =
  for field in default(paramsAsTuple(p(nil))).fields:
    when field is Atom:
      inc result

type
  ValidTraitor = concept f
    for field in f.fields:
      field.paramTypeAt(0) is Atom
      ##field.returnType isnot Atom
      atomCount(typeof(field)) == 1


  Traitor[Traits: ValidTraitor] = ref object of RootObj
    id: uint16

  TypedTraitor[T; Traits: ValidTraitor] {.final.} = ref object of Traitor[Traits]
    data: T

proc removeAtom(stmt, typ: NimNode): bool =
  for i, node in stmt:
    case node.kind
    of nnkSym:
      if node.eqIdent"Atom":
        stmt[i] = typ
        return true
    else:
      result = result or removeAtom(node, typ)


macro emitPointerProc(name, prc, typ: typed): untyped =
  let procType = prc.getType

  result = genast():
    proc() {.nimcall.} = discard



  let call = newCall(name.strVal)

  for i, def in procType[1..^1]:
    if i == 0:
      if not procType[1].eqIdent"void":
        result.params[0] = procType[1]
    else:
      let
        arg = genSym(nskParam, "param" & $i)
        theTyp =
          if def == bindSym"Atom":
            nnkBracketExpr.newTree(bindSym"TypedTraitor", typ, prc[0][1])
          else:
            def

      if theTyp.removeAtom(typ) or def.eqIdent"Atom":
        call.add nnkDotExpr.newTree(arg, ident"data")
      else:
        call.add arg
      result.params.add newIdentDefs(arg, theTyp)

  result[^1] = call

  #[ Emit:
    proc(traitor: Traitor[prc[0][1]], ...): prc[^1] =
      let conv = cast[TypedTraitor[typ, prc[0][1]]](traitor)
      name(conv.data, ...)
  ]#

macro callImpl*(trait: Traitor, name: untyped, table: seq[pointer], args: typed): untyped =
  let
    tupl = trait.getTypeInst[^1].getTypeImpl()
    tuplArity = tupl.len
  var
    procType: NimNode
    offset = 0
  for field in tupl:
    if field[0].eqIdent name:
      procType = field[1]
      break
    inc offset

  if procType.kind == nnkEmpty:
    error("No procedure named '" & $name & "' found for '" & trait.getType.repr & "'.", name)

  discard procType.removeAtom(trait.getType)

  let theCast = nnkCast.newTree(procType):
    genast(trait, table, offset, tuplArity, procType):
      table[trait.id * tuplArity + offset]
  result = newCall(theCast, trait)

  for x in args:
    result.add x

template implTrait(trait: typedesc[tuple]) =
  var traitVtable: seq[pointer]
  var counter {.compileTime.} = 0u16
  converter toTraitor[T](val: sink T): Traitor[trait] =
    const id = counter
    static: inc counter
    once:
      for name, field in default(trait).fieldPairs:
        traitVtable.add cast[pointer](emitPointerProc(name, field, T))
    TypedTraitor[T, trait](id: id, data: val)

  template `.()`(traitor: Traitor[trait], name: untyped, args: varargs[typed]): untyped {.inject.} =
    callImpl(traitor, name, traitVtable, args)

{.experimental: "dotOperators".}


type
  MyTrait = tuple[
    doThing: proc(_: Atom) {.nimcall.},
    doOtherThing: proc(_: Atom, _: float){.nimcall.}]
  MyOtherTrait = tuple[
    doThing: proc(_: Atom) {.nimcall.},
    doOtherThing: proc(_: Atom, _: string){.nimcall.}

    ]

implTrait MyTrait
implTrait MyOtherTrait

proc doThing(i: int) = echo i * 30
proc doOtherThing(a: int, b: float) = echo a + int(b)
proc doOtherThing(a: int, b: string) = echo b, ": ", a

proc doThing(f: float) = echo f
proc doOtherThing(a, b: float) = echo a * b
proc doOtherThing(a: float, b: string) = echo b, ": ", a

var a: Traitor[MyTrait] = 100
a.doThing()
a.doOtherThing(3d)
a = 3d

a.doThing()
a.doOtherThing(3d)

var b: Traitor[MyOtherTrait] = 30
b.doThing()
b.doOtherThing("int")
b = 3d

b.doThing()
b.doOtherThing("float")

type MyType = object
  x, y: int

proc `=destroy`(typ: MyType) = echo "Buh bye"

proc doThing(typ: MyType) = echo (typ.x + typ.y) * 30
proc doOtherThing(typ: MyType, b: float) = echo typ.x + int(b)
proc doOtherThing(typ: MyType, b: string) = echo b, ": ", typ.y

a = MyType(x: 20, y: 1)
a.doThing()
a.doOtherThing(3d)

b = MyType(x: 20, y: 1)
b.doThing()
b.doOtherThing("My own Type!")

