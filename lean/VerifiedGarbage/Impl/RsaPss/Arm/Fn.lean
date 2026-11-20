module

public import VerifiedGarbage.Impl.RsaPss.Arm.Table
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# RSASSA-PSS on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Residue.Arm.scrubF`):
the stack its contract reserves zeroed, where its frames and those of the
functions it calls (the private or public operation, and the hash functions
of its tables) kept the key's values, the encoded message and the hash
functions' states, then the registers a callee may change set to constants,
but the 32 bits of the result, and the flags. Each takes the functions it
calls: those of every table of `MdHash` (`f`, the hash function's; `g`,
MGF1's) and the RSA operation, as its registration maps over their
implementations. Signing's frames use 3624 bytes, which is no frame size of
the model, so its contract reserves, and its cleanup zeroes, the next one,
3632.
-/

@[expose] public section

namespace VG.Impl.RsaPss.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_rsa_pss_sign_precomputed`, calling `vg_rsa_private_checked_precomputed`
(`privC`, by its name `privN`). -/
def signPrecomputed (f : MdFns) (g : Impl.RsaOaep.Arm.Fns) (privN : String) (privC : Prog isa) : Prog isa :=
  scrubF 32 3632 (signP f g privN privC)

/-- `vg_rsa_pss_verify_precomputed`, calling a precomputed public operation
(`pubC`, by its name `pubN`). -/
def verifyPrecomputed (f : MdFns) (g : Impl.RsaOaep.Arm.Fns) (pubN : String) (pubC : Prog isa) : Prog isa :=
  scrubF 32 240 (Impl.RsaPss.Arm.verifyPrecomputed f g pubN pubC)

end VG.Impl.RsaPss.Arm.Fn
