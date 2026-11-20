module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# HMAC on RISC-V: the functions as emitted

HMAC's `init` and `finalize` for the streaming functions `H`, then their
cleanup, the caller-saved registers cleared (they return nothing).
`finalize` zeroes all the stack its frames use: its own frame and the `F`
bytes below it that `H`'s functions use (`Impl.Scrub.RISCV64.scrub`).
`init`, which wipes the long key's streaming state and digest in its frame
itself, zeroes only the runs of doublewords that the residue analysis
(`RISCV64.rtaint`) finds may differ between two runs
(`Impl.Scrub.RISCV64.scrubSel`): the `F` bytes below its frame, and the
slots above the key's state and digest where it keeps our caller's
registers.
-/

@[expose] public section

namespace VG.Impl.Hmac.Stream.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub scrubSel)

/-- `vg_hmac_<hash>_init` for the streaming functions `H`, as emitted. -/
def init (H : Hash) : Prog isa :=
  scrubSel 0 [(H.ibytes + H.F, [(0, H.F / 8), ((H.F + H.iso) / 8, (H.ibytes - H.iso) / 8)])] H.init

/-- `vg_hmac_<hash>_finalize` for the streaming functions `H`, as emitted. -/
def finalize (H : Hash) : Prog isa := scrub 0 (H.fbytes + H.F) H.finalize

end VG.Impl.Hmac.Stream.RISCV64.Fn
