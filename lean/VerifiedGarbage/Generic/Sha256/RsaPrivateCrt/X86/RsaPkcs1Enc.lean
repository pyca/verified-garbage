module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified

/-! # RSAES-PKCS1-v1_5 decryption with implicit rejection on x86 -/

@[expose] public section

namespace VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPkcs1Enc

open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Backend) (c : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.decryptApi.artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPkcs1Enc.X86.Dec.decryptCode v c
    stack := Proof.RsaPkcs1Enc.X86.Dec.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Dec.code_verified v c
    spSafe := Proof.RsaPkcs1Enc.X86.Dec.code_sp v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPkcs1Enc
