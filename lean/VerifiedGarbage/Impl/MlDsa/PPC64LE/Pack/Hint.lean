module

public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream

/-!
# ML-DSA on PPC64LE: `vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`

Both follow Algorithms 20 and 21 (the spec's `hintBitPack` and
`hintBitUnpack`) step by step, as on 32-bit ARM
(`Impl/MlDsa/Arm/Pack/Hint.lean`). They may leak the hint, and branch and
index memory on it; each first zeroes its output, whose contents are then a
function of the hint alone. The model branches only on a register being
zero: a comparison `x < y` of small numbers is the sign bit of `x - y`
(`ltBit`). Each first zero-extends `omega` (a `u32`, whose register's upper
bits the ABI leaves unspecified) in `r5`. They use only volatile registers,
and no stack.

* `hintBitPack(h = r3, hlen = r4, omega = r5, y = r6, len = r7)`: zeroes
  the `len` bytes of `y`; then, with the index in `r11`, for each of the `k`
  polynomials (`r9` counting down; `r10` pointing at `y[ω + i]`) and each of
  their 256 coefficients (`r12` = `j`, `r3` walking the words), stores `j`
  to `y[index]` and increments the index if the coefficient is not 0, and
  then stores the index to `y[ω + i]`.
* `hintBitUnpack(y = r3, len = r4, omega = r5, h = r6, hlen = r7)`: zeroes
  the `hlen` words of `h`; then, with the index in `r11`, for each of the
  `k` polynomials (`r12` counting down; `r10` pointing at `y[ω + i]`, and
  `r6` at polynomial `i` of `h`), unless a check failed (the index is at
  most `ω`), checks the bound `y[ω + i]` (in `r8`) against the index and
  `ω`, and sets the coefficients `y[index]` of the polynomial up to it, each
  but the first after checking that it is greater than the previous one;
  then checks that the bytes from the index up to `ω` are zero. A failed
  check sets the index to 256 (more than `ω`, and than any byte), which ends
  the loop it is in and skips the rest; the return value is 1 if the index
  is at most `ω`, 0 otherwise.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Pack

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- `t ← 1` if `x < y`, `0` otherwise, for `x` and `y` less than `2⁶³`: the
sign bit of `x - y`. -/
def ltBit (t x y : Reg) : List Instr := [.sub t x y, .lsr .d t t 63]

/-- `omega` zero-extended in `r5`. -/
def zextOmega : List Instr := [.lsl .r5 .r5 32, .lsr .d .r5 .r5 32]

/-! ## `vg_mldsa_hint_bit_pack` -/

/-- `k = len - ω` into `r4`; zero the `len` bytes of `y` (`r6`), with `r10`
walking them and `r9` counting. -/
def hbpZero : Prog isa :=
  .seq (.block (zextOmega ++ ([.sub .r4 .r7 .r5, mov .r9 .r7, .li .r0 0, mov .r10 .r6] : List Instr)))
    (.loop (.block [.stb .r0 .r10 0, .addi .r10 .r10 1, .subi .r9 .r9 1]) (.nonzero .d .r9))

/-- Coefficient `j = r12` of the polynomial, the word at `r3`: if it is not
0, `y[index] ← j` and the index is incremented; then `r8 ← j + 1 - 256`. -/
def hbpCoef : Prog isa :=
  .seq (.block [.load .w .r8 .r3 0])
    (.seq (.ite (.zero .w .r8) (.block []) (.block [.add .r8 .r6 .r11, .stb .r12 .r8 0, .addi .r11 .r11 1]))
      (.block [.addi .r3 .r3 4, .addi .r12 .r12 1, .subi .r8 .r12 256]))

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hbpPoly : Prog isa :=
  .seq (.block [.li .r12 0])
    (.seq (.loop hbpCoef (.nonzero .d .r8)) (.block [.stb .r11 .r10 0, .addi .r10 .r10 1, .subi .r9 .r9 1]))

/-- The `k` polynomials (`k` from `r4`), from `r10 = y + ω`, the index `r11`
from 0. -/
def hbpMain : Prog isa :=
  .seq (.block [mov .r9 .r4, .add .r10 .r6 .r5, .li .r11 0]) (.loop hbpPoly (.nonzero .d .r9))

def hintBitPack : Prog isa := .seq hbpZero hbpMain

/-! ## `vg_mldsa_hint_bit_unpack` -/

/-- `k = len - ω` into `r12`; zero the `hlen` words of `h` (`r6`), with `r10`
walking them and `r9` counting; the index `r11` then 0. -/
def hbuZero : Prog isa :=
  .seq (.block (zextOmega ++ ([.sub .r12 .r4 .r5, mov .r9 .r7, .li .r0 0, mov .r10 .r6] : List Instr)))
    (.seq (.loop (.block [.store .w .r0 .r10 0, .addi .r10 .r10 4, .subi .r9 .r9 1]) (.nonzero .d .r9))
      (.block [.li .r11 0]))

/-- A failed check: the index becomes 256. -/
def hbuFail : Prog isa := .block [.li .r11 256]

/-- Set coefficient `y[index]` of the polynomial at `r6`, and increment the
index. -/
def hbuSet : List Instr :=
  [.add .r9 .r3 .r11, .lbz .r9 .r9 0, .lsl .r9 .r9 2, .add .r9 .r6 .r9, .li .r0 1, .store .w .r0 .r9 0,
    .addi .r11 .r11 1]

/-- `r0 ≠ 0` iff the index is less than the bound `r8`. -/
def hbuMore : List Instr := ltBit .r0 .r11 .r8

/-- A coefficient after the first: `y[index - 1] < y[index]`, or fail. -/
def hbuNext : Prog isa :=
  .seq (.block (([.add .r9 .r3 .r11, .lbz .r0 .r9 0, .subi .r9 .r9 1, .lbz .r9 .r9 0] : List Instr) ++
      ltBit .r0 .r9 .r0))
    (.seq (.ite (.zero .d .r0) hbuFail (.block hbuSet)) (.block hbuMore))

/-- The coefficients of the polynomial, while the index is less than the
bound `r8`: the first, then the others. -/
def hbuCoefs : Prog isa :=
  .seq (.block hbuMore)
    (.ite (.zero .d .r0) (.block [])
      (.seq (.block (hbuSet ++ hbuMore)) (.ite (.zero .d .r0) (.block []) (.loop hbuNext (.nonzero .d .r0)))))

/-- Polynomial `i`, unless a check failed: the bound `y[ω + i]`, checked
against the index and `ω`, and the coefficients up to it. -/
def hbuPoly : Prog isa :=
  .seq (.block (ltBit .r0 .r5 .r11))
    (.ite (.zero .d .r0)
      (.seq (.block (([.lbz .r8 .r10 0] : List Instr) ++ ltBit .r0 .r8 .r11))
        (.ite (.zero .d .r0) (.seq (.block (ltBit .r0 .r5 .r8)) (.ite (.zero .d .r0) hbuCoefs hbuFail)) hbuFail))
      (.block []))

/-- The `k` polynomials, from `r10 = y + ω`. -/
def hbuMain : Prog isa :=
  .seq (.block [.add .r10 .r3 .r5])
    (.loop (.seq hbuPoly (.block [.addi .r10 .r10 1, .addi .r6 .r6 1024, .subi .r12 .r12 1])) (.nonzero .d .r12))

/-- The bytes from the index up to `ω` are zero, or fail. -/
def hbuTrail : Prog isa :=
  .seq (.block (ltBit .r0 .r11 .r5))
    (.ite (.zero .d .r0) (.block [])
      (.loop (.seq (.block [.add .r9 .r3 .r11, .lbz .r9 .r9 0])
        (.seq (.ite (.zero .d .r9) (.block [.addi .r11 .r11 1]) hbuFail) (.block (ltBit .r0 .r11 .r5))))
        (.nonzero .d .r0)))

/-- `r3 ← 1` if the index is at most `ω`, 0 otherwise. -/
def hbuRet : List Instr := [.sub .r0 .r5 .r11, .lsr .d .r0 .r0 63, .li .r3 1, .sub .r3 .r3 .r0]

def hintBitUnpack : Prog isa := .seq hbuZero (.seq hbuMain (.seq hbuTrail (.block hbuRet)))

end VG.Impl.MlDsa.PPC64LE.Pack
