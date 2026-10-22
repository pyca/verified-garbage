module

public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch

/-!
# Preparing a key context's first sixteen powers in place, on 256-bit registers

`vg_aes_gcm_prepare16`: `H'`–`H'¹⁶` from the hash subkey at `ctx + 240`, as
the stitched loops compute them (`Stitch.setupG`), already in the prepared
form and paired as the context holds them, stored as pairs 0–7: the first
part of `Prepare.prepare`, for the loops that read no other power. No calls,
no stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Prepare16

open VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)

/-- The 16 prepared powers into the context at `rdi`, from its hash subkey:
the registers of `setupG` hold pairs 7–0 (`pregs`), so their reverse is
stored from pair 0. -/
def prepare16 : Prog isa :=
  .block (setupG ++ storesK .rdi pregs.reverse 8 ++ ([.vop .vzeroupper] : List Instr))

end VG.Impl.Gcm.X86_64.Prepare16
