module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat

/-! # RSAES-OAEP with SHA-224 and MGF1 with SHA-1 on x86: decryption, for each Sha256 backend, Sha1 backend and implementation of the CRT -/

@[expose] public section

namespace VG.Generic.Sha256.Sha1.RsaPrivateCrt.X86.RsaOaepSha224Mgf1Sha1

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (w : Proof.Sha1.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha224 Spec.Mgf1.sha1).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("sha1", w.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaOaep.X86.Dec.decCode (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha1 w) c
    stack := Proof.RsaOaep.X86.Dec.stackBytes
    verified := Proof.RsaOaep.X86.Dec.dec_verified (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha1 w) (Proof.RsaOaep.X86.Dec.dec_sat _ _) c
    spSafe := Proof.RsaOaep.X86.Dec.code_sp (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha1 w) c
    features := (v.features ++ w.features.filter (!v.features.contains ·)) ++
      c.features.filter (!(v.features ++ w.features).contains ·) }]

end VG.Generic.Sha256.Sha1.RsaPrivateCrt.X86.RsaOaepSha224Mgf1Sha1
