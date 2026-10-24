module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Dsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Dsa.verifyApi.artifact PPC64LE.target {
    notes := ["The key's public part is checked first (sizes, oddness, p mod q = 1, the orders of g \
        and y), branching only on it. The verification computes w = s^(q − 2) mod q, g^u1 and y^u2 \
        with the fixed-window secret-exponent power of the RSA code on PPC64LE, and keeps the range \
        checks of r and s as a mask: signature and digest do not affect the leakage trace."]
    code := Impl.Dsa.PPC64LE.Verify.verify
    verified := Proof.Dsa.PPC64LE.verify_verified }]

end VG.Artifacts.Dsa.PPC64LE
