module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
public import VerifiedGarbage.Spec.Dsa.Prevalidated

/-!
# DSA prevalidated verification on PPC64LE: the contract on the registers

`vpContract`: `vg_dsa_verify_prevalidated`, with `vg_dsa_verify`'s
arguments, result and public data (`vContract`), for a key that passes the
specification's validation.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `vg_dsa_verify_prevalidated`, on the registers and the stack. -/
def vpContract : Contract isa where
  pre s := vContract.pre s ∧ Spec.Dsa.validatePublicKeyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) = true
  post := vContract.post
  pub := vContract.pub

end VG.Proof.Dsa.PPC64LE
