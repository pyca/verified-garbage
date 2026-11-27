module

public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# AES-OCB on RISC-V, as emitted

`vg_aes_ocb_init` (AES-GCM's key expansion, `Impl.AesGcm.RISCV64.init`), `vg_aes_ocb_seal` and `vg_aes_ocb_open`, each on its stack scratch
(`Impl.StackScratch.RISCV64`), followed by its cleanup
(`Impl.Scrub.RISCV64.scrubAll`), which zeroes the stack its frames use and
clears the caller-saved registers but the result's bits.
-/

@[expose] public section

namespace VG.Impl.AesOcb.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_aes_ocb_init`, then its cleanup. -/
def init : Prog isa :=
  scrubAll 0 2560 (withStackScratch 2560 .a3 VG.Impl.AesGcm.RISCV64.init)

/-- `vg_aes_ocb_seal`, then its cleanup. -/
def «seal» : Prog isa :=
  scrubAll 0 2592 (withStackScratchArgs 2592 2 VG.Impl.AesOcb.RISCV64.«seal»)

/-- `vg_aes_ocb_open`, then its cleanup. -/
def «open» : Prog isa :=
  scrubAll 32 2592 (withStackScratchArgs 2592 2 VG.Impl.AesOcb.RISCV64.«open»)

end VG.Impl.AesOcb.RISCV64.Fn
