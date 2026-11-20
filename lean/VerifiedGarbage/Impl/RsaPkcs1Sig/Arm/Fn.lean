module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# RSASSA-PKCS1-v1_5 verification on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Residue.Arm.scrubF`):
the 2192 bytes of stack its contract reserves zeroed, then the registers a
callee may change set to constants, but the 32 bits of the result, and the
flags. Each takes the precomputed public operation it calls (`pd`, by its
name `pdName`), as its registration maps over its implementations.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_rsa_pkcs1_verify_precomputed`. -/
def verifyPrecomputed (pdName : String) (pd : Prog isa) : Prog isa :=
  scrubF 32 2192 (Precomputed.code pdName pd)

/-- `vg_rsa_pkcs1_recover_precomputed`. -/
def recoverPrecomputed (pdName : String) (pd : Prog isa) : Prog isa :=
  scrubF 32 2192 (RecoverPrecomputed.code pdName pd)

end VG.Impl.RsaPkcs1Sig.Arm.Fn
