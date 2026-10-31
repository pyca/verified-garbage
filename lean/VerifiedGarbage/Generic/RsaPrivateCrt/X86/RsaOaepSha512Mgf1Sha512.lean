module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat

/-! # RSAES-OAEP with SHA-512 and MGF1 with SHA-512 on x86: decryption, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86.RsaOaepSha512Mgf1Sha512

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (c : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512 Spec.Mgf1.sha512).artifact X86.target {
    suffix := c.suffix
    code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha512 Proof.RsaOaep.X86.sha512 c
    stack := Proof.RsaOaep.X86.Dec.stackBytes
    verified := Proof.RsaOaep.X86.Dec.dec_verified Proof.RsaOaep.X86.sha512 Proof.RsaOaep.X86.sha512 (Proof.RsaOaep.X86.Dec.dec_sat _ _) c
    spSafe := Proof.RsaOaep.X86.Dec.code_sp Proof.RsaOaep.X86.sha512 Proof.RsaOaep.X86.sha512 c
    features := c.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaOaepSha512Mgf1Sha512
