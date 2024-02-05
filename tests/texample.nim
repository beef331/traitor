import ../traitor
type
  Clickable = distinct tuple[ # Always use a distinct tuple interface to make it clean and cause `implTrait` requires it
      over: proc(a: Atom, x, y: int): bool {.nimcall.}, # Notice we use `Atom` as the first parameter and it's always the only `Atom`
      onClick: proc(a: Atom) {.nimcall.}]
  UnimplementedTrait = distinct tuple[
    overloaded: ( # We can add overloads by using a tuple of procs
      proc(a: var Atom) {.nimcall.},
      proc(a: Atom, b: int) {.nimcall.})
    ]

  Button = object
    x, y, w, h: int

  Radio = object
    x, y, r: int

implTrait Clickable

proc over(btn: Button, x, y: int): bool =
  btn.x < x and (btn.x + btn.w) > x and btn.y < y and (btn.y + btn.h) > y

proc onClick(btn: Button) =
  echo "Clicked a button"

proc over(radio: Radio, x, y: int): bool =
  radio.r >= (abs(radio.x - x) + abs(radio.y - y))

proc onClick(radio: Radio) = echo "Clicked a radio"

emitConverter Button, Clickable # Emit a `converter` for `Button` -> `Traitor[Clickable]`

type ClickObj[T] = TypedTraitor[T, Clickable]

var
  elements = [
    Traitor[Clickable] Button(w: 10, h: 20), # We can convert directly if we use `emitConvert`
    Button(x: 30, y: 30, w: 10, h: 10),
    Radio(x: 30, y: 30, r: 10).toTrait(Clickable) # Otherwise we need to convert with `toTrait(trait)`
  ]

assert elements[0].over(3, 3) # We can call procedures as if they're normal
assert elements[1].over(33, 33)
assert elements[2].over(30, 30)

for i, x in elements:
  if x of  TypedTraitor[Button, Clickable]: # We can use `of` to check if it's the given type
    assert i in [0, 1]
  elif x of ClickObj[Radio]:
    assert i == 2

assert elements[2].getData(Radio) == Radio(x: 30, y: 30, r: 10) # We can use `getData` to extract data
elements[2].getData(Radio).x = 0 # It emits a `var T` so it can be mutated
assert elements[2].getData(Radio).x == 0
