module

public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-CCM on x86-64: the functions as emitted

`vg_aes_ccm_seal` and `vg_aes_ccm_open` over the CBC-MAC update `u` and
CTR function `c` they call, in a frame of their working space, then their
cleanup (`Impl.Scrub.X86_64.scrubAll v rb 2624`): every vector register at
the level `v` and every caller-saved register but the result's cleared,
and their whole frame wiped.
-/

@[expose] public section

namespace VG.Impl.AesCcm.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `vg_aes_ccm_seal`, as emitted. -/
def «seal» (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Impl.Aes.X86_64.Ctr32) : Prog isa :=
  scrubAll v 0 2624 (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (X86_64.«seal» u c))

/-- `vg_aes_ccm_open`, as emitted. -/
def «open» (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Impl.Aes.X86_64.Ctr32) : Prog isa :=
  scrubAll v 32 2624 (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (X86_64.«open» u c))

end VG.Impl.AesCcm.X86_64.Fn
