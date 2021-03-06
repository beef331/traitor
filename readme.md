# Traitor

A macro heavy trait library made from bordem.


## What does it do?!

Traitor allows one to use to use the new Nim concepts to describe interfaces that can ensure types implement procedures.
It also enables runtime dispatch of procedures of those concepts.

The following is an example:

```nim
import traitor

type
  Clickable = concept
    proc over(a: Self, x, y: int): bool
    proc onClick(a: Self)

  Button = object
    x, y, w, h: int

  Radio {.byref.} = object # Objects smaller than 24 bytes need `{.byref.}`
    x, y, r: int

implTraits Clickable:
  proc over(btn: Button, x, y: int): bool =
    btn.x < x and (btn.x + btn.w) > x and btn.y < y and (btn.y + btn.h) > y

  proc onClick(btn: Button) =
    echo "Clicked a button"

  proc over(radio: Radio, x, y: int): bool =
    radio.r >= (abs(radio.x - x) + abs(radio.y - y))
  
  proc onClick(radio: Radio) = echo "Clicked a radio"

setupTraits Clickable # Implements the required logic for `Clickable` to be used

var
  elements = [
    Button(w: 10, h: 20).toImpl Clickable,
    Button(x: 30, y: 30, w: 10, h: 10), # Our converters enable this magic!
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
```

By default traitor uses dynamically allocated buffers, if one wants to do fixed size buffers one can do `-d:traitorBufferSize=YourSize` and it'll use `array[YourSize, byte]` as a backer to hold the data.
Alternatively one can use `withTraitorBufferSize` to temporaily change the buffer size.
Though doing this will emit distinct objects that cannot be used homogenously with any other objects.



