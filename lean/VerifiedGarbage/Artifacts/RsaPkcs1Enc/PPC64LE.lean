module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PKCS #1 v1.5 encryption with a precomputed RSA public key on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact PPC64LE.target {
    notes := ["This implementation writes `EM = 0x00 || 0x02 || PS || 0x00 || M` to its frame, collecting \
      whether `PS` has a zero byte without branching, calls `vg_rsa_public_precomputed_checked` with the \
      cached modulus values into `out`, then masks `out` and the result to zeros if `PS` has a zero byte \
      and zeroes `EM`. It uses 2224 bytes of stack, its frame (that of `vg_rsa_pkcs1_verify_precomputed`): \
      the call uses none."]
    code := Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Enc.PPC64LE.Enc.code_verified }]

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
