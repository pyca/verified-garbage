module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Constant-time byte comparison on RISC-V

`vg_ct_eq(a = a0, a_len = a1, b = a2, b_len = a3)`: the same algorithm as
the PPC64LE implementation (`VG.Impl.Ct.PPC64LE`). The lengths are compared
first; if they are equal, the XORs of the bytes at each offset are ORed
together into `a4`, and the result is `(a4 - 1) >> 63`, which is 1 iff `a4`
is zero. The bytes are loaded one at a time (`lbu`), so no access is
misaligned. The branches are on the lengths only.
-/

@[expose] public section

namespace VG.Impl.Ct.RISCV64
open VG.RISCV64

def step : List Instr := [
  .add .t0 .a0 .a5, .load .b .t1 .t0 0,
  .add .t0 .a2 .a5, .load .b .t2 .t0 0,
  .logic .xor .t1 .t1 .t2, .logic .or .a4 .a4 .t1,
  .addi .a5 .a5 1, .sub .a7 .a5 .a1]

def finish : Prog isa := .block [.addi .a4 .a4 (-1), .shift .srl .d .a0 .a4 63]

def equal : Prog isa :=
  .seq (.block [.li .a5 0])
    (.seq (.ite (.zero .a1) (.block []) (.loop (.block step) (.nonzero .a7))) finish)

def eq : Prog isa :=
  .seq (.block [.li .a4 0, .sub .a7 .a1 .a3])
    (.ite (.zero .a7) equal (.block [.li .a0 0]))

end VG.Impl.Ct.RISCV64
