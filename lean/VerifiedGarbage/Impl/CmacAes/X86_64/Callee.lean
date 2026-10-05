import VerifiedGarbage.Impl.CmacAes.X86_64
import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi

/-!
# The implementations of `vg_cmac_aes_update` on x86-64

A function that calls `vg_cmac_aes_update` (streaming AES-CMAC's `absorb`,
and AES-CCM's and AES-SIV's functions) takes the implementation it calls,
an `Update`, and is emitted once for each (`Generic/CmacAesUpdate/X86_64/`):
the chaining by calls of an implementation of `vg_aes_ctr32`
(`Impl.CmacAes.X86_64.update`), or the one in AES-NI registers
(`AesNi.update`).
-/

namespace VG.Impl.CmacAes.X86_64

open VG.X86_64

/-- An implementation of `vg_cmac_aes_update` to call: its symbol and its code. -/
structure Update where
  name : String
  code : Prog isa

end VG.Impl.CmacAes.X86_64
