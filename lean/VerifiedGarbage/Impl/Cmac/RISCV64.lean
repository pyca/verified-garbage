module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# CMAC on RISC-V: doubling a block a byte at a time

`dbl n c src dst` doubles the block of `n` bytes at `s1 + src` into
`s1 + dst` (NIST SP 800-38B §6.1 steps 2 and 3), for AES-CMAC (`n = 16`,
`c = 0x87`) and TDEA-CMAC (`n = 8`, `c = 0x1b`), a byte at a time, since
the contracts state no alignment for the block: byte 0 into `t1`, the mask
`c` or 0 of its top bit into `t2` (that bit, minus 1, masking `c`, XORed
with `c`), bytes 0 to `n - 2` (`dblStep`), and byte `n - 1` shifted and
XORed with the mask.
-/

@[expose] public section

namespace VG.Impl.Cmac.RISCV64

open VG.RISCV64

/-- One byte of the doubling, `i < n - 1`: byte `i + 1` of the block at
`s1 + src` loaded into `t3`, and byte `i` (in `t1`) shifted left by one bit
with the top bit of byte `i + 1` entering on the right, stored to
`s1 + dst + i`; byte `i + 1` then moves to `t1`. -/
def dblStep (src dst i : Nat) : List Instr :=
  [.load .b .t3 .s1 (src + i + 1), .shift .sll .d .t1 .t1 1, .shift .srl .d .t4 .t3 7,
   .logic .or .t1 .t1 .t4, .store .b .t1 .s1 (dst + i), .addi .t1 .t3 0]

/-- The block of `n` bytes at `s1 + src`, doubled (`VG.Spec.Cmac.dbl n`, with
`R_b`'s last byte `c`), to `s1 + dst` (`dst` is `src`, or at least
`src + n`). -/
def dbl (n : Nat) (c : Int) (src dst : Nat) : List Instr :=
  [.load .b .t1 .s1 src, .shift .srl .d .t2 .t1 7, .addi .t2 .t2 (-1), .logicImm .and .t2 .t2 c,
   .logicImm .xor .t2 .t2 c] ++
    (List.range (n - 1)).flatMap (dblStep src dst) ++
    [.shift .sll .d .t1 .t1 1, .logic .xor .t1 .t1 .t2, .store .b .t1 .s1 (dst + (n - 1))]

end VG.Impl.Cmac.RISCV64
