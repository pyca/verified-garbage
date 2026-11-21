module

public import VerifiedGarbage.Impl.CmacAes.Stream.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# Streaming AES-CMAC on RISC-V: the functions as emitted

`vg_cmac_aes_init`, `vg_cmac_aes_absorb` and `vg_cmac_aes_finish`, each
with its 2304 bytes of working space in a frame of its own
(`Impl.StackScratch.RISCV64.withStackScratch`), then its cleanup
(`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers cleared (they
return nothing), and the 2304 bytes of stack its frames use zeroed, the
working space with them.
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)
open VG.Impl.StackScratch.RISCV64 (withStackScratch)

/-- `vg_cmac_aes_init`, as emitted. -/
def init : Prog isa := scrubAll 0 2304 (withStackScratch 2304 .a3 Impl.CmacAes.Stream.RISCV64.init)

/-- `vg_cmac_aes_absorb`, as emitted. -/
def absorb : Prog isa := scrubAll 0 2304 (withStackScratch 2304 .a5 Impl.CmacAes.Stream.RISCV64.absorb)

/-- `vg_cmac_aes_finish`, as emitted. -/
def finish : Prog isa := scrubAll 0 2304 (withStackScratch 2304 .a4 Impl.CmacAes.Stream.RISCV64.finish)

end VG.Impl.CmacAes.Stream.RISCV64.Fn
