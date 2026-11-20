module

public import VerifiedGarbage.Impl.Rc4.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # RC4 on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrubSel rb fs`: of the
stack its frames use, only the runs of doublewords `fs` that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs zeroed), and
the caller-saved registers cleared but the `rb` bits of the result, so that
it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Rc4.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubSel)

/-- `Spec.Rc4.initApi`'s function as emitted. -/
def init : Prog isa :=
  scrubSel 32 [] Impl.Rc4.RISCV64.init

/-- `Spec.Rc4.applyApi`'s function as emitted. -/
def apply : Prog isa :=
  scrubSel 0 [] Impl.Rc4.RISCV64.apply

end VG.Impl.Rc4.RISCV64.Fn
