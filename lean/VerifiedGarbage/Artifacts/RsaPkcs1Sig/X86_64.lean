import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-! # RSASSA-PKCS1-v1_5 (RFC 8017 §8.2) on x86-64: verification and recovery

Signing calls `vg_rsa_private_checked`, which has a variant per
implementation of the CRT, so it is generic over them
(`Generic/RsaPrivateCrt/X86_64/RsaPkcs1Sig.lean`). -/

namespace VG.Artifacts.RsaPkcs1Sig.X86_64

open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts : List Artifact := [
  { Spec.RsaPkcs1Sig.verifyApi with
    target := X86_64.target
    doc := Spec.RsaPkcs1Sig.verifyApi.doc
      (notes := ["This implementation computes `s^e mod n` with `vg_rsa_public_checked` into its frame, \
        writes EMSA-PKCS1-v1_5's encoding of `digest` beside it, and compares the two: RFC 8017 \
        §8.2.2 as written, which accepts exactly when BoringSSL's check does. It uses 2144 bytes of \
        stack: a frame of 2136 bytes, which holds both encodings and the stack arguments of the call, \
        and the call's return address."])
    code := Impl.RsaPkcs1Sig.X86_64.Verify.code pubChecked.name pubChecked.code
    contract := Spec.RsaPkcs1Sig.verifyContract X86_64.abi verStack
    stack := verStack
    verified := Ver.code_verified pubChecked
    spSafe := Ver.code_spSafe pubChecked },
  { Spec.RsaPkcs1Sig.recoverApi with
    target := X86_64.target
    doc := Spec.RsaPkcs1Sig.recoverApi.doc
      (notes := ["This implementation computes `EM = s^e mod n` with `vg_rsa_public_checked` into its \
        frame, writes EMSA-PKCS1-v1_5's encoding of the last `out_len` bytes of `EM` beside it, and \
        releases those bytes if the two are equal, as OpenSSL's `ossl_rsa_verify` recovers: the same \
        result as BoringSSL's. It uses 2144 bytes of stack, as `vg_rsa_pkcs1_verify` does."])
    code := Impl.RsaPkcs1Sig.X86_64.Recover.code pubChecked.name pubChecked.code
    contract := Spec.RsaPkcs1Sig.recoverContract X86_64.abi verStack
    stack := verStack
    verified := Rec.code_verified pubChecked
    spSafe := Rec.code_spSafe pubChecked }]

end VG.Artifacts.RsaPkcs1Sig.X86_64
