module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.AArch64.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-! # RSASSA-PSS verification on AArch64 with a precomputed key, with the hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AllMdHash.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64 (verify_ok OK)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if h : OK vs then [
    Spec.RsaPss.verifyPrecomputedTableApi.artifact AArch64.target {
      suffix := Emit.qualifiedName "" [("rsa", c.suffix)]
      tables := [("hash", Proof.MdHashTable.AArch64.tables vs), ("mgf1", Proof.HashTable.AArch64.tables vs)]
      code := Impl.RsaPss.AArch64.verifyC (Proof.MdHashTable.AArch64.fnsOf vs) (Proof.HashTable.AArch64.fnsOf vs)
        (pdOf c).name (pdOf c).code
      stack := Proof.RsaPss.AArch64.Sgn.stk 624
      verified := verify_ok h c
      features := c.features }]
  else []

end VG.Generic.RsaPublicPrecomputed.AllMdHash.AArch64.RsaPss
