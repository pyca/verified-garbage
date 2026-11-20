module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# Streaming TDEA-CMAC on RISC-V: the functions as emitted

`vg_cmac_triple_des_stream_init`, `_absorb` and `_finish`, each with its
working space in a frame of its own
(`Impl.StackScratch.RISCV64.withStackScratch`), then its cleanup
(`Impl.Scrub.RISCV64.scrub`): the caller-saved registers cleared (they
return nothing), and all the stack its frames use zeroed, the working space
and the frame of ECB's serial code below it, which holds a copy of the key
schedule.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)
open VG.Impl.StackScratch.RISCV64 (withStackScratch)

/-- `vg_cmac_triple_des_stream_init`, as emitted. -/
def init : Prog isa := scrub 0 1584 (withStackScratch 640 .a3 Impl.CmacTripleDes.Stream.RISCV64.streamInit)

/-- `vg_cmac_triple_des_absorb`, as emitted. -/
def absorb : Prog isa := scrub 0 1632 (withStackScratch 688 .a4 Impl.CmacTripleDes.Stream.RISCV64.absorb)

/-- `vg_cmac_triple_des_finish`, as emitted. -/
def finish : Prog isa := scrub 0 1584 (withStackScratch 640 .a3 Impl.CmacTripleDes.Stream.RISCV64.finish)

end VG.Impl.CmacTripleDes.Stream.RISCV64.Fn
