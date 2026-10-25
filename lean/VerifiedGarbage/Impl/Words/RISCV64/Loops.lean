module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Loops over buffers in RISC-V code

Loops for buffers too long to unroll (their lemmas are in
`Proof/Framework/RISCV64/Loops.lean`):
* `copyLoop`: `cnt` bytes copied, one at a time, the pointers advancing;
* `fillLoop`: `cnt` doublewords stored from a register, the pointer advancing.

Each runs its body at least once: `cnt` is nonzero on entry.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- Copy `cnt` bytes from `src` to `dst`, a byte at a time through `tmp`. -/
def copyLoop (tmp src dst cnt : Reg) : Prog isa :=
  .loop (.block [.load .b tmp src 0, .store .b tmp dst 0, .addi src src 1, .addi dst dst 1,
    .addi cnt cnt (-1)]) (.nonzero cnt)

/-- Store `v` in the `cnt` doublewords at `ptr`. -/
def fillLoop (v ptr cnt : Reg) : Prog isa :=
  .loop (.block [.store .d v ptr 0, .addi ptr ptr 8, .addi cnt cnt (-1)]) (.nonzero cnt)

end VG.Impl.Words.RISCV64
