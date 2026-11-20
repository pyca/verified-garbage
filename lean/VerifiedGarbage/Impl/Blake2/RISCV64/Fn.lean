module

public import VerifiedGarbage.Impl.Blake2.RISCV64.Stream
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# BLAKE2b and BLAKE2s on RISC-V, as emitted

Each streaming function, then its cleanup (`Impl.Scrub.RISCV64.scrub rb W`):
the zeroing of the `W` bytes of stack its frames use (none for `init`, the
336-byte frame of `update` and `finalize`), and the clearing of the
caller-saved registers, `a0` included (none returns a value), so that it
returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Blake2.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_blake2b_init`, as emitted. -/
def initB : Prog isa := scrub 0 0 (Stream.init Spec.Blake2.b)

/-- `vg_blake2b_update`, as emitted. -/
def updateB : Prog isa := scrub 0 336 (Stream.update Spec.Blake2.b)

/-- `vg_blake2b_finalize`, as emitted. -/
def finalizeB : Prog isa := scrub 0 336 (Stream.finalize Spec.Blake2.b)

/-- `vg_blake2s_init`, as emitted. -/
def initS : Prog isa := scrub 0 0 (Stream.init Spec.Blake2.s)

/-- `vg_blake2s_update`, as emitted. -/
def updateS : Prog isa := scrub 0 336 (Stream.update Spec.Blake2.s)

/-- `vg_blake2s_finalize`, as emitted. -/
def finalizeS : Prog isa := scrub 0 336 (Stream.finalize Spec.Blake2.s)

end VG.Impl.Blake2.RISCV64.Fn
