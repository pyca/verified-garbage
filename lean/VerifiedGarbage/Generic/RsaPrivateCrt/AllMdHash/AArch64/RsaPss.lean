module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.AArch64.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RSASSA-PSS signing on AArch64, with the hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AllMdHash.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64 (sign_ok OK)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if h : OK vs then [
    Spec.RsaPss.signTableApi.artifact AArch64.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.AArch64.tables vs), ("mgf1", Proof.HashTable.AArch64.tables vs)]
      code := Impl.RsaPss.AArch64.signC (Proof.MdHashTable.AArch64.fnsOf vs) (Proof.HashTable.AArch64.fnsOf vs)
        (privOf c).name (privOf c).code
      stack := Proof.RsaPss.AArch64.Sgn.stk (privOf c).stack
      verified := sign_ok h c
      features := c.features }]
  else []

end VG.Generic.RsaPrivateCrt.AllMdHash.AArch64.RsaPss
