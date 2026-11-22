module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Sign
public import VerifiedGarbage.Impl.Rsa.Arm.WipeTwo

/-!
# RSASSA-PKCS1-v1_5 on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.Arm.scrubAll`):
the 2192 bytes of stack its contract reserves zeroed, then the registers a
callee may change set to constants, but the 32 bits of the result, and the
flags. Each takes the precomputed public operation it calls (`pd`, by its
name `pdName`), as its registration maps over its implementations.

Signing with the key's precomputed values keeps 4616 bytes below the stack
pointer (its frames, 1176 bytes, and the private operation's 3440), more than
one frame of the model holds (fewer than 4096), so its cleanup zeroes them in
two frames, of 4080 and 584 bytes (`Impl.Rsa.Arm.WipeTwo.scrubAll2`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_rsa_pkcs1_verify_precomputed`. -/
def verifyPrecomputed (pdName : String) (pd : Prog isa) : Prog isa :=
  scrubAll 32 2192 (Precomputed.code pdName pd)

/-- `vg_rsa_pkcs1_recover_precomputed`. -/
def recoverPrecomputed (pdName : String) (pd : Prog isa) : Prog isa :=
  scrubAll 32 2192 (RecoverPrecomputed.code pdName pd)

/-- `vg_rsa_pkcs1_sign_precomputed`, calling `vg_rsa_private_checked_precomputed`
(`priv`, by its name `privN`). -/
def signPrecomputed (privN : String) (priv : Prog isa) : Prog isa :=
  Impl.Rsa.Arm.WipeTwo.scrubAll2 32 4080 584 (Sign.code true privN priv)

end VG.Impl.RsaPkcs1Sig.Arm.Fn
