module

public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# AES-GCM-SIV on RISC-V, as emitted

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`, each on its stack scratch
(`Impl.StackScratch.RISCV64`), followed by its cleanup
(`Impl.Scrub.RISCV64.scrubAll`), which zeroes the stack its frames use and
clears the caller-saved registers but the result's bits.
Their frames use 5904 bytes of stack, of which their scratch is 3856.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_aes_gcm_siv_seal`, then its cleanup. -/
def «seal» : Prog isa :=
  scrubAll 0 5904 (withStackScratchArgs 3856 0 VG.Impl.AesGcmSiv.RISCV64.«seal»)

/-- `vg_aes_gcm_siv_open`, then its cleanup. -/
def «open» : Prog isa :=
  scrubAll 32 5904 (withStackScratchArgs 3856 0 VG.Impl.AesGcmSiv.RISCV64.«open»)

end VG.Impl.AesGcmSiv.RISCV64.Fn
