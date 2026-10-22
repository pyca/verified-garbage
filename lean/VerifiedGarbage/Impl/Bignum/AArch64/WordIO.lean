module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-!
# Big-endian bytes a word at a time (AArch64)

`loadW` and `storeW` do what `loadBE` and `storeBE` do, but eight bytes at a
time (`ldr` and `rev`, `rev` and `str`) when the number of bytes `k` is a
multiple of eight, as an RSA modulus's usually is: word `w - 1 - j` of the
array is bytes `8 j` to `8 j + 7`, most significant first. Other lengths
take `loadBE` and `storeBE`. The branch and every address depend only on
`k` and the pointers.
-/

@[expose] public section

namespace VG.Impl.Bignum.AArch64

open VG VG.AArch64

/-- The `k` bytes at `x1` (`k` in `x2`, a multiple of 8, at least 8) into the
`k / 8` words of the array at `x8`: from the most significant, into the word
before `x5`, which starts at the array's end. -/
def loadWords : Prog isa :=
  .seq (.block [.add .x .x5 .x8 .x2])
    (.loop (.block [ld .x3 .x1, .rev .x3 .x3, .subImm .x .x5 .x5 8, st .x3 .x5, next .x1, .subImm .x .x2 .x2 8])
      (.nonzero .x .x2))

/-- The `w` words at `x8`, each and'ed with `x15`, to the `k = 8 w` bytes
ending at `x1` (`k` in `x9`), most significant first: word `j` (at `x5`) to
the eight bytes before `x1`. -/
def storeWords : Prog isa :=
  .seq (.block [mov .x5 .x8])
    (.loop (.block [ld .x3 .x5, .logic .and .x .x3 .x3 .x15, .rev .x3 .x3, .subImm .x .x1 .x1 8, st .x3 .x1, next .x5,
        .subImm .x .x9 .x9 8])
      (.nonzero .x .x9))

/-- `loadBE`, by `loadWords` when `k` (`x2`) is a multiple of 8. -/
def loadW : Prog isa :=
  .seq (.block [movi .x6 7, .logic .and .x .x4 .x2 .x6]) (.ite (.zero .x .x4) loadWords loadBE)

/-- `storeBE`, by `storeWords` when `k` (`x9`) is a multiple of 8. -/
def storeW : Prog isa :=
  .seq (.block [movi .x6 7, .logic .and .x .x2 .x9 .x6]) (.ite (.zero .x .x2) storeWords storeBE)

end VG.Impl.Bignum.AArch64
