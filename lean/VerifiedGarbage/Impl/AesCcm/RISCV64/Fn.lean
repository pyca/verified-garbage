module

public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# AES-CCM on RISC-V, as emitted

`vg_aes_ccm_seal` and `vg_aes_ccm_open`, each on its stack scratch
(`Impl.StackScratch.RISCV64`), followed by its cleanup
(`Impl.Scrub.RISCV64.scrubAll`), which zeroes the stack its frames use and
clears the caller-saved registers but the result's bits.
-/

@[expose] public section

namespace VG.Impl.AesCcm.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_aes_ccm_seal`, then its cleanup. -/
def «seal» : Prog isa :=
  scrubAll 0 2592 (withStackScratchArgs 2592 2 VG.Impl.AesCcm.RISCV64.«seal»)

/-- `vg_aes_ccm_open`, then its cleanup. -/
def «open» : Prog isa :=
  scrubAll 32 2592 (withStackScratchArgs 2592 2 VG.Impl.AesCcm.RISCV64.«open»)

end VG.Impl.AesCcm.RISCV64.Fn
