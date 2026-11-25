# Subtraction modulo p = 2^521 - 1

Written 2026-11-25 after the code (`subOps`, commit 18a6f54d), at a reviewer's
request. Nothing recorded before that commit derives it.

Let 0 <= a, b < p, nine 64-bit words. The nine-word subtraction leaves
D = a - b + 2^576 B with B the borrow, so B = 1 exactly when a < b.

The value wanted is r = a - b + B p, and 0 <= r < p. Put p = 2^521 - 1:
r = a - b + 2^521 B - B = D - B + (2^521 - 2^576) B, so r = D - B modulo 2^521
(2^576 is a multiple of 2^521). As 0 <= r < 2^521, r is (D - B) mod 2^521.

So what is added back, p, is a 1 taken at the bottom and bits at and above
2^521 that are then cut. One chain of nine subtract-with-borrow of zero takes
the borrow as its input, and one mask of the top word cuts. No case is left
over: B = 0 gives D < p unchanged.

Alternatives, counted as instructions after the 9 + 9 loads (and not the
stores), as the model's `Op`s allow:

* this: 9 subtract, 1 zero, 9 subtract the borrow, 1 constant, 1 mask = 21
* add p back under a mask (as the sum does): 9 subtract, 1 zero, 1 constant,
  1 mask from the borrow, 1 mask of the top word, 9 add = 22
* compute D and D + p, select by the borrow: needs a conditional select, which
  `Op` lacks, and 9 of them: at least 9 + 9 + 9 = 27
* a + (p - b), then reduce: 9 more for p - b, and the sum's own correction

The first is the fewest and needs no constant of eight words in a register.
The working leads to the code there is.
