module

public import VerifiedGarbage.Impl.Md5.RISCV64.Stream
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# MD5 on RISC-V, as emitted

Each streaming function, then its cleanup (`Impl.Scrub.RISCV64.scrub rb W`):
the zeroing of the `W` bytes of stack its frames use (none for `init`, the
144-byte frame of `update` and `finalize`), and the clearing of the
caller-saved registers, `a0` included (none returns a value), so that it
returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Md5.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_md5_init`, as emitted. -/
def init : Prog isa := scrub 0 0 Stream.init

/-- `vg_md5_update`, as emitted. -/
def update : Prog isa := scrub 0 144 Stream.update

/-- `vg_md5_finalize`, as emitted. -/
def finalize : Prog isa := scrub 0 144 Stream.finalize

end VG.Impl.Md5.RISCV64.Fn
