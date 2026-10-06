import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-! # RSASSA-PKCS1-v1_5 (RFC 8017 §8.2) on AArch64: verification and recovery

Signing calls `vg_rsa_private_checked`, which has a variant per
implementation of the CRT, so it is generic over them
(`Generic/RsaPrivateCrt/AArch64/RsaPkcs1Sig.lean`); verification with
precomputed values is generic over the implementations of
`vg_rsa_public_precomputed_checked`
(`Generic/RsaPublicPrecomputed/AArch64/RsaPkcs1Sig.lean`). -/

namespace VG.Artifacts.RsaPkcs1Sig.AArch64

open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts : List Artifact := [
  { Spec.RsaPkcs1Sig.verifyApi with
    target := AArch64.target
    doc := Spec.RsaPkcs1Sig.verifyApi.doc
      (notes := ["This implementation computes `s^e mod n` with `vg_rsa_public_checked` into its frame, \
        writes EMSA-PKCS1-v1_5's encoding of `digest` beside it, and compares the two: RFC 8017 \
        §8.2.2 as written, which accepts exactly when BoringSSL's check does. It uses 2144 bytes of \
        stack: a frame of 2128 bytes, which holds both encodings and the stack arguments of the call, \
        and 16 bytes below it for the call."])
    code := Impl.RsaPkcs1Sig.AArch64.Verify.code pubChecked.name pubChecked.code
    contract := Spec.RsaPkcs1Sig.verifyContract AArch64.abi (Ver.stk pubChecked.stack)
    stack := Ver.stk pubChecked.stack
    verified := Ver.code_verified pubChecked
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.RsaPkcs1Sig.recoverApi with
    target := AArch64.target
    doc := Spec.RsaPkcs1Sig.recoverApi.doc
      (notes := ["This implementation computes `EM = s^e mod n` with `vg_rsa_public_checked` into its \
        frame, writes EMSA-PKCS1-v1_5's encoding of the last `out_len` bytes of `EM` beside it, and \
        releases those bytes if the two are equal, as OpenSSL's `ossl_rsa_verify` recovers: the same \
        result as BoringSSL's. It uses 2144 bytes of stack, as `vg_rsa_pkcs1_verify` does."])
    code := Impl.RsaPkcs1Sig.AArch64.Recover.code pubChecked.name pubChecked.code
    contract := Spec.RsaPkcs1Sig.recoverContract AArch64.abi (Ver.stk pubChecked.stack)
    stack := Ver.stk pubChecked.stack
    verified := Rec.code_verified pubChecked
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaPkcs1Sig.AArch64
