module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc

/-! Montgomery cancellation with the known-zero low word omitted.
The carry into the second limb is obtained by comparing the old low word
with one. This is valid under the existing inverse condition. -/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.BlockedRedcFast
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
-- The cancelled low word is zero; its addition carries iff it was nonzero.
abbrev lowChain := BlockedRedc.cancelLowChain
abbrev cancel := BlockedRedc.cancel
abbrev redc := BlockedRedc.redc

end VG.Impl.Bignum.AArch64.BlockedRedcFast
