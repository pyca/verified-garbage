module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Verified
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
    verified := Proof.Dsa.PPC64LE.verify_verified },
  Spec.Dsa.signApi.artifact PPC64LE.target {
    notes := ["The key's public part is checked as for verification, branching only on it. Signing \
        compares g^x mod p with y, computes r = (g^k mod p) mod q, w = k^(q − 2) mod q and \
        s = w (z + x r) mod q with the fixed-window secret-exponent power of the RSA code on PPC64LE, \
        and keeps the checks of x, k, r and s as a mask that selects the signature or zeros: the \
        private key, the nonce and the digest do not affect the leakage trace."]
    code := Impl.Dsa.PPC64LE.Sign.sign
    verified := Proof.Dsa.PPC64LE.sign_verified },
  Spec.Dsa.checkParametersApi.artifact PPC64LE.target {
    notes := ["The domain is checked as the key's public part is for verification (sizes, oddness, \
        p mod q = 1, the order of g), with the fixed-window power of the RSA code on PPC64LE, \
        branching only on the domain, which is public."]
    code := Impl.Dsa.PPC64LE.Params.checkParameters
    verified := Proof.Dsa.PPC64LE.checkParameters_verified }]

end VG.Artifacts.Dsa.PPC64LE
