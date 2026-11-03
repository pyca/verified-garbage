module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64

/-!
# A number shifted right in place on RISC-V

`shrWords n o sh` shifts the `n`-word number at `[o]` of the working space
(at `s0`) right by `0 < sh < 64` bits, a word at a time from the lowest,
through `t0` and `t1`: for P-521, whose 66-byte encodings hold 7 bits more
than its numbers (the hash's integer `e`, RFC 6979's candidates).
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass.RISCV64

/-- Word `j` of `[o] = [o] >> sh` (`0 < sh < 64`), of `n` words, through
`t0` and `t1`: word `j` shifted right, or'd with word `j + 1` shifted left
by `64 - sh`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  ldAt .t0 wb (o + 8 * j) ++ [.shift .srl .d .t0 .t0 sh] ++
    (if j + 1 < n then ldAt .t1 wb (o + 8 * (j + 1)) ++ [.shift .sll .d .t1 .t1 (64 - sh), .logic .or .t0 .t0 .t1]
    else []) ++
    sdAt .t0 wb (o + 8 * j)

/-- `[o] = [o] >> sh` (`0 < sh < 64`), `n` 64-bit words, from the lowest. -/
def shrWords (n o sh : Nat) : List Instr := (List.range n).flatMap (shrStep n o sh)

end VG.Impl.Ecdh.RISCV64
