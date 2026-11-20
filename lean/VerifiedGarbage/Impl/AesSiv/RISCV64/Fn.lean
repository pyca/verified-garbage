module

public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# AES-SIV on RISC-V, as emitted

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, each on its stack scratch
(`Impl.StackScratch.RISCV64`), followed by its cleanup
(`Impl.Scrub.RISCV64.scrub`), which zeroes the stack its frames use and
clears the caller-saved registers but the result's bits.
-/

@[expose] public section

namespace VG.Impl.AesSiv.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_aes_siv_init`, then its cleanup. -/
def init : Prog isa :=
  scrub 0 2560 (withStackScratch 2560 .a3 VG.Impl.AesSiv.RISCV64.init)

/-- `vg_aes_siv_encrypt`, then its cleanup. -/
def encrypt : Prog isa :=
  scrub 0 2576 (withStackScratch 2576 .a7 VG.Impl.AesSiv.RISCV64.encrypt)

/-- `vg_aes_siv_decrypt`, then its cleanup. -/
def decrypt : Prog isa :=
  scrub 32 2576 (withStackScratch 2576 .a7 VG.Impl.AesSiv.RISCV64.decrypt)

end VG.Impl.AesSiv.RISCV64.Fn
