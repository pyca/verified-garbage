module

public import VerifiedGarbage.Impl.Words.RISCV64.Loops

/-!
# Copies a doubleword at a time when the buffers allow it (RISC-V)

`copyAny` copies `cnt` bytes, a multiple of 8, between buffers: a
doubleword at a time (`copyLoopW`) when both pointers are 8-byte aligned,
which RISC-V needs for `ld` and `sd` not to trap, and otherwise a byte at
a time (`copyLoop`). The choice depends on the pointers alone. Its lemma is
in `Proof/Framework/RISCV64/CopyFast.lean`.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- Copy `cnt` doublewords from `src` to `dst`, through `tmp`. -/
def copyLoopW (tmp src dst cnt : Reg) : Prog isa :=
  .loop (.block [.load .d tmp src 0, .store .d tmp dst 0, .addi src src 8, .addi dst dst 8,
    .addi cnt cnt (-1)]) (.nonzero cnt)

/-- Copy `cnt` bytes (a nonzero multiple of 8) from `src` to `dst`, through
`tmp`: a doubleword at a time if both are 8-byte aligned, else a byte at a
time. -/
def copyAny (tmp src dst cnt : Reg) : Prog isa :=
  .seq (.block [.logic .or tmp src dst, .logicImm .and tmp tmp 7])
    (.ite (.zero tmp) (.seq (.block [.shift .srl .d cnt cnt 3]) (copyLoopW tmp src dst cnt))
      (copyLoop tmp src dst cnt))

end VG.Impl.Words.RISCV64
