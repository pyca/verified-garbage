module
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.CmacAes.X86_64
public import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi


/-!
# The implementations of `vg_cmac_aes_update` on x86-64

A function that calls `vg_cmac_aes_update` (streaming AES-CMAC's `absorb`,
and AES-CCM's and AES-SIV's functions) takes the implementation it calls,
an `Update`, and is emitted once for each (`Generic/CmacAesUpdate/X86_64/`):
the chaining by calls of an implementation of `vg_aes_ctr32`
(`Impl.CmacAes.X86_64.update`), or the one in AES-NI registers
(`AesNi.update`), or a choice between the two by the number of blocks
(`hybrid`).
-/

@[expose] public section

namespace VG.Impl.CmacAes.X86_64

open VG.X86_64

/-- An implementation of `vg_cmac_aes_update` to call: its symbol and its code. -/
structure Update where
  name : String
  code : Prog isa

/-- The chaining in AES-NI registers (`AesNi.update`, out of line) for two
blocks or more (`n`, `r8`), where loading the round keys once pays for
itself, and otherwise the chaining by a call of `c` (`update c`). -/
def hybrid (c : Impl.Aes.X86_64.Ctr32) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 2)]) (Code.iteCold .ae AesNi.update (update c))

end VG.Impl.CmacAes.X86_64
