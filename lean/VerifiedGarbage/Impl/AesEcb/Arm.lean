module

public import VerifiedGarbage.Impl.Aes.Arm.Blocks
public import VerifiedGarbage.Impl.CallWipe.ArmStack
public import VerifiedGarbage.Impl.Zeroize.Arm

/-!
# AES-ECB on ARMv7

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` call `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks` by `callWipeStack`, which copies `scratch` (the
word on the stack) into its frame for the call, then zero the first
`scratchUsed` bytes of `scratch` with `vg_zeroize` (`Proof/AesEcb/Arm.lean`).
-/

@[expose] public section

namespace VG.Impl.AesEcb.Arm

open VG.Arm
open VG.Impl.Aes.Arm (scratchUsed)

/-- A call of `name`, whose code is `body`, then of `vg_zeroize`'s code
(as the internal `vg_zeroize_core`) on the
first `scratchUsed` bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.ArmStack.callWipeStack 1 0 scratchUsed name body "vg_zeroize_core" Impl.Zeroize.Arm.zeroize

/-- `vg_aes_ecb_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_encrypt_blocks" Impl.Aes.Arm.encryptBlocks

/-- `vg_aes_ecb_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_decrypt_blocks" Impl.Aes.Arm.decryptBlocks

end VG.Impl.AesEcb.Arm
