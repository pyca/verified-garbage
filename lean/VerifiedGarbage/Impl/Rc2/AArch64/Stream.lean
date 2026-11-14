module

public import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey

/-! # Streaming RC2-CBC on baseline AArch64

`vg_rc2_cbc_init(key = x0, key_len = x1, effective_bits = x2, iv = x3,
iv_len = x4, ctx = x5, scratch = x6)` checks the lengths, returning 1, 2 or 3
in `x0` for the first that is invalid, copies the IV to `ctx + 128` and calls
`vg_rc2_expand_key` to write the schedule to `ctx`, and returns 0.

Nothing is kept across a call, which is last, so only caller-saved registers
are used; the return address (`x30`), which the call replaces, is saved in a
16-byte stack frame around the code that calls.

The model has no flags: the range checks are a subtraction and a shift
tested with `cbnz`. Every branch and address depends only on the pointers
and lengths.

`copy`, the byte copy the update functions used, stays for ECDSA's
verification (`Impl/Ecdsa/AArch64/VerifyHash.lean`).
-/

@[expose] public section

namespace VG.Impl.Rc2.AArch64.Stream

open VG.AArch64

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- One byte from `[src + so]` to `[dst + dd]`, advancing both pointers and
counting `cnt` down. -/
def copyBody (src : Reg) (so : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : List Instr :=
  [.ldrb .x9 src so, .strb .x9 dst dd, .addImm .x src src 1, .addImm .x dst dst 1,
    .subImm .x cnt cnt 1]

/-- Copies `cnt` bytes from `src + so` to `dst + dd`; afterwards `src` and
`dst` have advanced by the count and `cnt` is 0. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : Prog isa :=
  .ite (.zero .x cnt) (.block [])
    (.loop (.block (copyBody src so dst dd cnt)) (.nonzero .x cnt))

/-! ## `init` -/

def keyCall : Prog isa := .call "vg_rc2_expand_key" expandKey

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx`, `scratch`. -/
def initArgs : List Instr :=
  [.ldr .x .x8 .x3 0, .str .x .x8 .x5 128, mov .x3 .x5, mov .x4 .x6]

/-- The IV, the key schedule, and 0, inside the frame saving `x30`. -/
def initMain : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block [.movz .x .x0 0 0]))

/-- `x8 ≠ 0` unless `key_len` is in 1..=128: `(key_len - 1) >> 7`. -/
def checkKey : List Instr := [.subImm .x .x8 .x1 1, .lsr .x .x8 .x8 7]

/-- `x8 ≠ 0` unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr := [.subImm .x .x8 .x2 1, .lsr .x .x8 .x8 10]

/-- `x8 ≠ 0` unless `iv_len` is 8. -/
def checkIv : List Instr := [.subImm .x .x8 .x4 8]

def init : Prog isa :=
  .seq (.block checkKey) (.ite (.nonzero .x .x8) (.block [.movz .x .x0 1 0])
    (.seq (.block checkBits) (.ite (.nonzero .x .x8) (.block [.movz .x .x0 2 0])
      (.seq (.block checkIv) (.ite (.nonzero .x .x8) (.block [.movz .x .x0 3 0])
        (.frame (.push .x30) initMain (.pop .x30)))))))

end VG.Impl.Rc2.AArch64.Stream
