module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common

/-!
# ML-DSA on PPC64LE: `vg_mldsa_sample_in_ball`

`sampleInBall(ctilde = r3, len = r4, tau = r5, c = r6, scratch = r7) -> r3`
(see `Common.lean` for the layout), as on 32-bit ARM: it squeezes 272 bytes
of SHAKE256 of the `len` bytes of `c̃` (2 blocks; the least bound of FIPS 204
Appendix C is 221 bytes), zeroes `c`, and runs `SampleInBall`'s loop over
the 264 bytes after the first 8, with `r3` at the byte, `r4` at `c[i]`, `r5`
= `i` (from `256 - τ`), the sign bits not yet used in `r9` (the first 8
bytes, as a little-endian doubleword, shifted right once per coefficient
set), `r6` counting down and `r7` = `q - 2`: while `i < 256`, a byte `j ≤ i`
(in `r8`) sets `c[i] ← c[j]` and `c[j] ← ±1` (`1 + s (q - 2)` for the next
sign bit `s`: 1, or `q - 1`), and increments `i`. It returns `i >> 8`: 1 if
`i = 256`, and 0 otherwise.

Its branches and addresses depend on the SHAKE256 output, a function of
`c̃`, which the contract lets it leak.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sample

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- The 256 coefficients of `c` zeroed, through `r4` and `r12`, `r6` counting. -/
def bZero : Prog isa :=
  .seq (.block [.li .r12 0, mov .r4 .r30, .li .r6 256])
    (.loop (.block [.store .w .r12 .r4 0, .addi .r4 .r4 4, .subi .r6 .r6 1]) (.nonzero .d .r6))

/-- The sign bits in `r9`, `i = 256 - τ` in `r5`, `r4` at `c[i]`, `r3` at the
byte after the sign bits, `r6` = 264 and `r7` = `q - 2`. -/
def bSetup : List Instr :=
  [.load .d .r9 .r31 840, .li .r5 256, .sub .r5 .r5 .r27, .lsl .r4 .r5 2, .add .r4 .r30 .r4,
    .addi .r3 .r31 848, .li .r6 264, .lis .r7 0x7F, .ori .r7 .r7 0xDFFF]

/-- `c[i] ← c[j]`, `c[j] ← ±1`, the sign bits shifted, `i` incremented. -/
def bSet : List Instr :=
  [.lsl .r10 .r8 2, .add .r10 .r30 .r10, .load .w .r11 .r10 0, .store .w .r11 .r4 0, .lsl .r12 .r9 63,
    .lsr .d .r12 .r12 63, .mul .r12 .r12 .r7, .addi .r12 .r12 1, .store .w .r12 .r10 0, .lsr .d .r9 .r9 1,
    .addi .r4 .r4 4, .addi .r5 .r5 1]

/-- The byte `j` at `r3`, into `r8`, accepted unless `i < j`. -/
def bTry : Prog isa :=
  .seq (.block [.lbz .r8 .r3 0, .sub .r11 .r5 .r8, .lsr .d .r11 .r11 63])
    (.ite (.zero .d .r11) (.block bSet) (.block []))

def bBody : Prog isa :=
  .seq (.block [.subi .r12 .r5 256, .lsr .d .r12 .r12 63])
    (.seq (.ite (.zero .d .r12) (.block []) bTry) (.block [.addi .r3 .r3 1, .subi .r6 .r6 1]))

def bLoop : Prog isa := .seq (.block bSetup) (.loop bBody (.nonzero .d .r6))

def sampleInBall : Prog isa :=
  .seq (.block (pro .r7 .r6 .r3 [mov .r28 .r4] (zext32 .r27 .r5)))
    (.seq (sponge 136 272) (.seq bZero (.seq bLoop (.block (retJ ++ epi)))))

end VG.Impl.MlDsa.PPC64LE.Sample
