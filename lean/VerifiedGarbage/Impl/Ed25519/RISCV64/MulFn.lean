module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Code

/-!
# `vg_gf25519_r32_mul` on RISC-V

`vg_gf25519_r32_mul(ws, o, a, b)` (`Spec/X25519/Field32.lean`: `ws` in `a0`,
the offsets in the low words of `a1`–`a3`) runs X25519's RISC-V product
(`Impl/X25519/RISCV64/R64.lean`'s `mulAt`: four 64-bit words by columns, with
`mul` and `mulhu`, then `lo + 38 hi` and the carry folded in twice) in its own
working space (bytes 768 to 1023 of `ws`), whose doublewords are aligned. The offsets are any bytes the contract allows, so the operands are
copied there a byte at a time (`unpackField`: `a` to byte 768, `b` to 800),
the product is computed at 832 (its eight words at 864), and its bytes are
copied to `o` (`packField`). The pointers to `a` and `b` are in `t4` and
`t5`, used before the product, and the pointer to `o` in `t2`, which the
product does not write. It uses only caller-saved
registers and no stack, and writes neither `a0` nor `ra`.

Every address is `ws` plus a constant or a public offset, and there are no
branches, so only `ws` and the offsets can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64

open VG.RISCV64

/-- Where the copies of the operands and the product are, in the function's
own working space. -/
def MA : Nat := 768
def MB : Nat := 800
def MO : Nat := 832

/-- The offsets zero-extended: only their low words are arguments. -/
def mulZext : List Instr :=
  [.shift .sll .d .a1 .a1 32, .shift .srl .d .a1 .a1 32, .shift .sll .d .a2 .a2 32,
    .shift .srl .d .a2 .a2 32, .shift .sll .d .a3 .a3 32, .shift .srl .d .a3 .a3 32]

/-- The pointers to `o` (`t2`), `a` (`t4`) and `b` (`t5`), and the working
space in `a3`, as the field code takes it. -/
def mulPtrs : List Instr := [.add .t2 .a0 .a1, .add .t4 .a0 .a2, .add .t5 .a0 .a3, .addi .a3 .a0 0]

/-- The operands into the own working space. -/
def mulIn : List Instr := unpackField .t4 MA 0 ++ unpackField .t5 MB 0

/-- `vg_gf25519_r32_mul`: the product of the elements at the offsets in
`a2` and `a3` into the one at the offset in `a1`. -/
def mulFn : Prog isa :=
  .seq (.block mulZext) <| .seq (.block (mulPtrs ++ mulIn)) <|
    .seq (Impl.X25519.RISCV64.R64.mulAt ACC MO MA MB) (.block (packField .t2 MO 0))

end VG.Impl.Ed25519.RISCV64
