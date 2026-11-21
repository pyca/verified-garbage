module

public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-! # The cleanup of code with more than 4080 bytes of stack, on AArch64

`scrubOfL` is `scrubOf` for code whose stack `scrubAllL` zeroes. -/

@[expose] public section

namespace VG.Impl.Scrub.AArch64

open VG VG.AArch64

/-- `scrubOf` for `4080 < W < 8176` bytes of stack: `c`, then its cleanup,
which clears the registers `c` may write (`Clear.of`) and zeroes that
stack (`scrubAllL`). -/
def scrubOfL (W rb : Nat) (c : Prog isa) : Prog isa := scrubAllL W rb (Clear.of c) c

end VG.Impl.Scrub.AArch64
