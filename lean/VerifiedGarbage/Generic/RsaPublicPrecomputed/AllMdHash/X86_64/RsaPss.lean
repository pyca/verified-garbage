module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86_64.Sat

/-! # RSASSA-PSS verification on x86-64, with the hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AllMdHash.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (verifyStack verify_ok chk_safe OK)

def artifacts (c : Proof.Rsa.X86_64.PublicImpl) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if h : OK vs then [
    Spec.RsaPss.verifyPrecomputedTableApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("rsa", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86_64.tables vs), ("mgf1", Proof.HashTable.X86_64.tables vs)]
      code := Impl.RsaPss.X86_64.verifyC (Proof.MdHashTable.X86_64.fnsOf vs) (Proof.HashTable.X86_64.fnsOf vs)
        c.name c.code
      stack := verifyStack
      verified := verify_ok h c
      spSafe := Code.all_of_allInstrs (Proof.RsaPss.X86_64.Pc.codeC_spAll (fun i hi => (chk_safe h i hi).1)
        (fun i hi => (chk_safe h i hi).2) c)
      features := c.features }]
  else []

end VG.Generic.RsaPublicPrecomputed.AllMdHash.X86_64.RsaPss
