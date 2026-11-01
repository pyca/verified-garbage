module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`

Both follow Algorithms 20 and 21 (the spec's `hintBitPack` and
`hintBitUnpack`) step by step, as on PPC64LE
(`Impl/MlDsa/PPC64LE/Pack/Hint.lean`). They may leak the hint, and branch and
index memory on it; each first zeroes its output, whose contents are then a
function of the hint alone. The code branches only on a register being
zero, as on PPC64LE: a comparison `x < y` of small numbers is the sign bit of `x - y`
(`ltBit`). Each first zero-extends `omega` (a `u32`, whose register's upper
bits the ABI leaves unspecified) in `a2`. They use only volatile registers,
and no stack.

* `hintBitPack(h = a0, hlen = a1, omega = a2, y = a3, len = a4)`: zeroes
  the `len` bytes of `y`; then, with the index in `t1`, for each of the `k`
  polynomials (`a6` counting down; `a7` pointing at `y[ω + i]`) and each of
  their 256 coefficients (`t2` = `j`, `a0` walking the words), stores `j`
  to `y[index]` and increments the index if the coefficient is not 0, and
  then stores the index to `y[ω + i]`.
* `hintBitUnpack(y = a0, len = a1, omega = a2, h = a3, hlen = a4)`: zeroes
  the `hlen` words of `h`; then, with the index in `t1`, for each of the
  `k` polynomials (`t2` counting down; `a7` pointing at `y[ω + i]`, and
  `a3` at polynomial `i` of `h`), unless a check failed (the index is at
  most `ω`), checks the bound `y[ω + i]` (in `a5`) against the index and
  `ω`, and sets the coefficients `y[index]` of the polynomial up to it, each
  but the first after checking that it is greater than the previous one;
  then checks that the bytes from the index up to `ω` are zero. A failed
  check sets the index to 256 (more than `ω`, and than any byte), which ends
  the loop it is in and skips the rest; the return value is 1 if the index
  is at most `ω`, 0 otherwise.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Pack

open VG.RISCV64

/-- `t ← 1` if `x < y`, `0` otherwise, for `x` and `y` less than `2⁶³`: the
sign bit of `x - y`. -/
def ltBit (t x y : Reg) : List Instr := [.sub t x y, .shift .srl .d t t 63]

/-- `omega` zero-extended in `a2`. -/
def zextOmega : List Instr := [.shift .sll .d .a2 .a2 32, .shift .srl .d .a2 .a2 32]

/-! ## `vg_mldsa_hint_bit_pack` -/

/-- `k = len - ω` into `a1`; zero the `len` bytes of `y` (`a3`), with `a7`
walking them and `a6` counting. -/
def hbpZero : Prog isa :=
  .seq (.block (zextOmega ++ ([.sub .a1 .a4 .a2, .addi .a6 .a4 0, .li .t0 0, .addi .a7 .a3 0] : List Instr)))
    (.loop (.block [.store .b .t0 .a7 0, .addi .a7 .a7 1, .addi .a6 .a6 (-1)]) (.nonzero .a6))

/-- Coefficient `j = t2` of the polynomial, the word at `a0`: if it is not
0, `y[index] ← j` and the index is incremented; then `a5 ← j + 1 - 256`. -/
def hbpCoef : Prog isa :=
  .seq (.block [.load .w .a5 .a0 0])
    (.seq (.ite (.zero .a5) (.block []) (.block [.add .a5 .a3 .t1, .store .b .t2 .a5 0, .addi .t1 .t1 1]))
      (.block [.addi .a0 .a0 4, .addi .t2 .t2 1, .addi .a5 .t2 (-256)]))

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hbpPoly : Prog isa :=
  .seq (.block [.li .t2 0])
    (.seq (.loop hbpCoef (.nonzero .a5)) (.block [.store .b .t1 .a7 0, .addi .a7 .a7 1, .addi .a6 .a6 (-1)]))

/-- The `k` polynomials (`k` from `a1`), from `a7 = y + ω`, the index `t1`
from 0. -/
def hbpMain : Prog isa :=
  .seq (.block [.addi .a6 .a1 0, .add .a7 .a3 .a2, .li .t1 0]) (.loop hbpPoly (.nonzero .a6))

def hintBitPack : Prog isa := .seq hbpZero hbpMain

/-! ## `vg_mldsa_hint_bit_unpack` -/

/-- `k = len - ω` into `t2`; zero the `hlen` words of `h` (`a3`), with `a7`
walking them and `a6` counting; the index `t1` then 0. -/
def hbuZero : Prog isa :=
  .seq (.block (zextOmega ++ ([.sub .t2 .a1 .a2, .addi .a6 .a4 0, .li .t0 0, .addi .a7 .a3 0] : List Instr)))
    (.seq (.loop (.block [.store .w .t0 .a7 0, .addi .a7 .a7 4, .addi .a6 .a6 (-1)]) (.nonzero .a6))
      (.block [.li .t1 0]))

/-- A failed check: the index becomes 256. -/
def hbuFail : Prog isa := .block [.li .t1 256]

/-- Set coefficient `y[index]` of the polynomial at `a3`, and increment the
index. -/
def hbuSet : List Instr :=
  [.add .a6 .a0 .t1, .load .b .a6 .a6 0, .shift .sll .d .a6 .a6 2, .add .a6 .a3 .a6, .li .t0 1, .store .w .t0 .a6 0,
    .addi .t1 .t1 1]

/-- `t0 ≠ 0` iff the index is less than the bound `a5`. -/
def hbuMore : List Instr := ltBit .t0 .t1 .a5

/-- A coefficient after the first: `y[index - 1] < y[index]`, or fail. -/
def hbuNext : Prog isa :=
  .seq (.block (([.add .a6 .a0 .t1, .load .b .t0 .a6 0, .addi .a6 .a6 (-1), .load .b .a6 .a6 0] : List Instr) ++
      ltBit .t0 .a6 .t0))
    (.seq (.ite (.zero .t0) hbuFail (.block hbuSet)) (.block hbuMore))

/-- The coefficients of the polynomial, while the index is less than the
bound `a5`: the first, then the others. -/
def hbuCoefs : Prog isa :=
  .seq (.block hbuMore)
    (.ite (.zero .t0) (.block [])
      (.seq (.block (hbuSet ++ hbuMore)) (.ite (.zero .t0) (.block []) (.loop hbuNext (.nonzero .t0)))))

/-- Polynomial `i`, unless a check failed: the bound `y[ω + i]`, checked
against the index and `ω`, and the coefficients up to it. -/
def hbuPoly : Prog isa :=
  .seq (.block (ltBit .t0 .a2 .t1))
    (.ite (.zero .t0)
      (.seq (.block (([.load .b .a5 .a7 0] : List Instr) ++ ltBit .t0 .a5 .t1))
        (.ite (.zero .t0) (.seq (.block (ltBit .t0 .a2 .a5)) (.ite (.zero .t0) hbuCoefs hbuFail)) hbuFail))
      (.block []))

/-- The `k` polynomials, from `a7 = y + ω`. -/
def hbuMain : Prog isa :=
  .seq (.block [.add .a7 .a0 .a2])
    (.loop (.seq hbuPoly (.block [.addi .a7 .a7 1, .addi .a3 .a3 1024, .addi .t2 .t2 (-1)])) (.nonzero .t2))

/-- The bytes from the index up to `ω` are zero, or fail. -/
def hbuTrail : Prog isa :=
  .seq (.block (ltBit .t0 .t1 .a2))
    (.ite (.zero .t0) (.block [])
      (.loop (.seq (.block [.add .a6 .a0 .t1, .load .b .a6 .a6 0])
        (.seq (.ite (.zero .a6) (.block [.addi .t1 .t1 1]) hbuFail) (.block (ltBit .t0 .t1 .a2))))
        (.nonzero .t0)))

/-- `a0 ← 1` if the index is at most `ω`, 0 otherwise. -/
def hbuRet : List Instr := [.sub .t0 .a2 .t1, .shift .srl .d .t0 .t0 63, .li .a0 1, .sub .a0 .a0 .t0]

def hintBitUnpack : Prog isa := .seq hbuZero (.seq hbuMain (.seq hbuTrail (.block hbuRet)))

end VG.Impl.MlDsa.RISCV64.Pack
