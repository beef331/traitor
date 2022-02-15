import ../traitor

type
  Clickable = concept
    proc over(a: Self, x, y: int): bool
    proc onClick(a: Self)

  Button = object
    x, y, w, h: int

  Radio {.byref.} = object # Objects smaller than 24 bytes need `{.byref.}`
    x, y, r: int

Button.implements Clickable
Radio.implements Clickable

proc over(btn: Button, x, y: int): bool {.impl.} = # `{.impl.}` subscribes it to the impl table
  btn.x < x and (btn.x + btn.w) > x and btn.y < y and (btn.y + btn.h) > y

impl: # Can be used as a block aswell
  proc onClick(btn: Button) =
    echo "Clicked a button"

  proc over(radio: Radio, x, y: int): bool =
    radio.r >= (abs(radio.x - x) + abs(radio.y - y))
  
  proc onClick(radio: Radio) = echo "Clicked a radio"

var
  elements = [
    Button(w: 10, h: 20).toImpl Clickable,
    Button(x: 30, y: 30, w: 10, h: 10), # Fully implemented interfaces implement converters
    Radio(x: 30, y: 30, r: 10)
  ]

assert elements[0].over(3, 3) # We can call procedures as if they're normal
assert elements[1].over(33, 33)
assert elements[2].over(30, 30)

for i, x in elements:
  if x of Button: # We can use `of` to check if it's the given type
    assert i in [0, 1]
  elif x of Radio:
    assert i == 2

assert (elements[2] as Radio) == Radio(x: 30, y: 30, r: 10) # We can use `as` to convert to a type
elements[2].to(Radio).x = 0 # We can also use `to` for chaining field access
assert elements[2].to(Radio).x == 0

checkImpls() # Ensures all types that implement concepts have procedures assigned for those concepts.