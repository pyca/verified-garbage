module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# XORing bytes of argument buffers in RISC-V code

`xorBytes`: the `n` bytes at `dst` XORed with those at `src`, in place, a
byte at a time (the contracts state no alignment for the buffers, see
`Impl/Words/RISCV64/Bytes.lean`); its lemma is in
`Proof/Framework/RISCV64/XorBytes.lean`.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- XOR the `n` bytes at `src` into those at `dst`, a byte at a time,
through `t` and `u`. -/
def xorBytes (t u dst src : Reg) (n : Nat) : List Instr :=
  (List.range n).flatMap fun i =>
    [.load .b t dst i, .load .b u src i, .logic .xor t t u, .store .b t dst i]

end VG.Impl.Words.RISCV64
