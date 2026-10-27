module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Products and powers in curve25519's field, in radix `2^32`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Gf25519R32.RISCV64

open VG.Spec.X25519.Field32 VG.Impl.Ed25519.RISCV64 VG.Proof.Ed25519.RISCV64

/-- How the product works. -/
def mulNotes : List String := ["Uses baseline integer instructions, only caller-saved registers \
  and no stack. The function copies its operands a byte at a time from `ws` plus each offset \
  (which the contract does not align) to bytes 768 and 800 of `ws`, runs X25519's RISC-V \
  product there (row by row, with `mul`, into sixteen 32-bit limbs at byte 864, then \
  `lo + 38 hi` and the carry folded in twice), and copies the result's bytes to `ws` plus `o`."]

/-- How the powers work. -/
def notes : List String := ["Uses baseline integer instructions, only caller-saved registers \
  and no stack. The function runs the addition chain of ref10's `fe_invert` up to \
  `a^(2^250 - 1)` (249 squarings, most in loops counted by `t1`, and 10 multiplications), with \
  X25519's RISC-V product inlined (row by row, with `mul`, then `lo + 38 hi` and the carry \
  folded in) and its temporaries in bytes 512 to 639."]

def artifacts : List Artifact := [
  mulApi.artifact RISCV64.target {
    notes := mulNotes
    code := mulFn
    verified := mulFn_verified },
  pow250Api.artifact RISCV64.target {
    notes := notes
    code := pow250Fn
    verified := pow250Fn_verified }]

end VG.Artifacts.Gf25519R32.RISCV64
