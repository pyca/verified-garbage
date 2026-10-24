module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Verified
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
    verified := Proof.Dsa.PPC64LE.checkParameters_verified },
  Spec.Dsa.deriveKeyApi.artifact PPC64LE.target {
    notes := ["The domain is checked as for `vg_dsa_check_parameters`, branching only on it. The \
        derivation computes y = g^x mod p with the fixed-window secret-exponent power of the RSA code on \
        PPC64LE, which is below p, and of order dividing q since g's is; it keeps the checks of y ≠ 0, \
        y ≠ 1 and 0 < x < q as a mask, and'ed into each octet of p||q||g||y||x as it goes to out: x and y \
        do not affect the leakage trace."]
    code := Impl.Dsa.PPC64LE.Derive.derive
    verified := Proof.Dsa.PPC64LE.deriveKey_verified },
  Spec.Dsa.randomSignApi.artifact PPC64LE.target {
    notes := ["Rejection sampling and signing retries are verified against the bounded random-tape \
        specification; each signing attempt calls `vg_dsa_sign`. A draw is copied, its first octet \
        masked, into the last octets of a zeroed nonce in the stack frame and compared with q by a \
        borrow chain without a branch: only the tape's length, the draws' acceptance and each \
        attempt's success affect the leakage trace. Every failure zeroes `out`, and every exit zeroes \
        the nonce. The nonvolatile registers, which hold the loop's state, are saved in the frame."]
    stack := 304
    code := Impl.Dsa.PPC64LE.RandomSign.code
    verified := Proof.Dsa.PPC64LE.randomSign_verified },
  Spec.Dsa.generateKeyApi.artifact PPC64LE.target {
    notes := ["The domain is checked by calling `vg_dsa_check_parameters`, branching only on it. x is \
        sampled as for `vg_dsa_sign_random`: each draw is copied, its first octet masked, into the last \
        octets of a zeroed nonce in the stack frame and compared with q by a borrow chain without a \
        branch, so only the tape's length and the draws' acceptance affect the leakage trace. An accepted \
        x is passed to `vg_dsa_derive_key`, which writes p||q||g||y||x or zeroes `out`. Every failure \
        zeroes `out`, and every exit zeroes the nonce. The nonvolatile registers, which hold the state, \
        are saved in the frame."]
    stack := 304
    code := Impl.Dsa.PPC64LE.Generate.code
    verified := Proof.Dsa.PPC64LE.generate_verified },
  Spec.Dsa.validatePublicKeyApi.artifact PPC64LE.target {
    notes := ["The key's public part is checked as for verification (sizes, oddness, p mod q = 1, the \
        orders of g and y), with the fixed-window power of the RSA code on PPC64LE, branching only on \
        the key, which is public."]
    code := Impl.Dsa.PPC64LE.Prevalidated.validate
    verified := Proof.Dsa.PPC64LE.validate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact PPC64LE.target {
    notes := ["As `vg_dsa_verify`, without the checks of the key the precondition establishes: only the \
        sizes are checked (which give q's significant octets), then p, R² mod p and q are loaded into \
        the working spaces and the verification is `vg_dsa_verify`'s, with the range checks of r and s \
        kept as a mask: signature and digest do not affect the leakage trace."]
    code := Impl.Dsa.PPC64LE.Prevalidated.verify
    verified := Proof.Dsa.PPC64LE.prevalidated_verified }]

end VG.Artifacts.Dsa.PPC64LE
