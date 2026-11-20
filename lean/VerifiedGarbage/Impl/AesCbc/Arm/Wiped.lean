module

public import VerifiedGarbage.Impl.AesCbc.Arm.Groups
public import VerifiedGarbage.Impl.CallWipe.ArmStack
public import VerifiedGarbage.Impl.Zeroize.Arm

/-!
# AES-CBC on ARMv7, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` call the CBC code, as the
internal functions `vg_aes_cbc_encrypt_unwiped` and
`vg_aes_cbc_decrypt_unwiped`, by `callWipeStack`, which copies the two stack
arguments (`n` and `scratch`) into its frame for the call, then zero the
whole of `scratch` (2176 bytes) with `vg_zeroize`
(`Proof/AesCbc/Arm/Wiped.lean`).
-/

@[expose] public section

namespace VG.Impl.AesCbc.Arm.Wiped

open VG.Arm

/-- A call of `name`, whose code is `body`, then of `vg_zeroize`'s code
(as the internal `vg_zeroize_core`) on the
2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.ArmStack.callWipeStack 2 4 2176 name body "vg_zeroize_core" Impl.Zeroize.Arm.zeroize

/-- `vg_aes_cbc_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_cbc_encrypt_unwiped" Impl.AesCbc.Arm.encrypt

/-- `vg_aes_cbc_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_cbc_decrypt_unwiped" Impl.AesCbc.Arm.decryptG

end VG.Impl.AesCbc.Arm.Wiped
