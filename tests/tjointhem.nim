import ../traitor
import balls


type
  Printer = distinct tuple[`$`: proc(_: Atom): string {.nimcall.}]
  Writer = distinct tuple[append: proc(_: Atom, s: var string) {.nimcall.}]

implTrait Printer
implTrait Writer

proc print(r: AnyTraitor[Printer], _: typedesc[Printer or void] = void): string =
  mixin `$`
  $r

proc print(r: AnyTraitor[Writer], _: typedesc[Writer or void] = void) = discard

proc write(s: var string, r: AnyTraitor[Writer]) =
  mixin append
  r.append(s)

type Debug = joinTraits(Printer, Writer)

implTrait Debug

proc append(val: auto, s: var string) = s.add $val

suite "Joined":
  test "Basic":
    var buff = ""
    var a = 10f.toTrait Debug
    check a.print(Printer) == $10f
    a.print(Writer)

    buff.write(a)
    check buff == $10f
    buff.setLen(0)

    a = (10, 20, "Hmm").toTrait Debug
    buff.write(a)
    check buff == $(10, 20, "Hmm")
    buff.setLen(0)

    buff.write (10, 20)
    check buff == $(10, 20)

    check (10, 20).print(Printer) == $(10, 20)
    (10, 20).print(Writer)
