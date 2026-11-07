module
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.CmacAes.AArch64
public import VerifiedGarbage.Impl.CmacAes.AArch64.Aese

/-!
# The implementations of `vg_cmac_aes_update` on AArch64

The chaining by calls of an implementation of `vg_aes_ctr32`
(`Impl.CmacAes.AArch64.update`), the one with the round keys in registers
(`Aese.update`), or a choice between the two by the number of blocks
(`hybrid`).
-/

@[expose] public section

namespace VG.Impl.CmacAes.AArch64
open VG.AArch64
/-- A whole-block CMAC chaining implementation for streaming callers. -/
structure Update where
  name : String
  code : Prog isa

/-- The chaining with the round keys in registers (`Aese.update`, out of
line) for two blocks or more (`n`, `x4`: `x9 = n >> 1` is not zero), where
loading the round keys once pays for itself, and otherwise the chaining by
a call of `c` (`update c`). -/
def hybrid (c : Impl.Aes.AArch64.Ctr32) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x4 1]) (Code.iteCold (.nonzero .x .x9) Aese.update (update c))

end VG.Impl.CmacAes.AArch64
