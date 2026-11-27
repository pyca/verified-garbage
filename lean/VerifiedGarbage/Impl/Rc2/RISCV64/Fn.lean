module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-! # RC2 on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrubSel rb fs`: of the
stack its frames use, only the runs of doublewords `fs` that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs zeroed), and
the caller-saved registers cleared but the `rb` bits of the result, so that
it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubSel)

/-- `Spec.Rc2.cbcInitApi`'s function as emitted. -/
def cbcInit : Prog isa :=
  scrubSel 32 [(608, [(72, 4)])]
    (Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.init)

/-- `Spec.Rc2.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubSel 0 []
    (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt)

/-- `Spec.Rc2.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubSel 0 []
    (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt)

end VG.Impl.Rc2.RISCV64.Fn
