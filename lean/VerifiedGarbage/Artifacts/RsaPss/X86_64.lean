module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86_64.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64

/-! # RSASSA-PSS signing on x86-64, with the hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaPss.X86_64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.RsaPss.X86_64 (signStack sign_ok signC_spAll enc_safe OK)

def artifacts (c : Proof.Rsa.X86_64.CrtImpl) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if h : OK vs then [
    Spec.RsaPss.signTableApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86_64.tables vs), ("mgf1", Proof.HashTable.X86_64.tables vs)]
      code := Impl.RsaPss.X86_64.signC (Proof.MdHashTable.X86_64.fnsOf vs) (Proof.HashTable.X86_64.fnsOf vs)
        (privOf c).name (privOf c).code
      stack := signStack
      verified := sign_ok h (privOf c).ok (privOf c).ct (X86_64.SpSafe.of_all (privOf c).spSafe) (privOf c).depth
      spSafe := Code.all_of_allInstrs (signC_spAll (fun i hi => (enc_safe h i hi).1) (fun i hi => (enc_safe h i hi).2)
        (X86_64.SpSafe.of_all (privOf c).spSafe))
      features := c.features }]
  else []

end VG.Artifacts.RsaPss.X86_64.RsaPrivateCrtAllMdHash

-- RSASSA-PSS verification on x86-64, with the hash functions as tables
namespace VG.Artifacts.RsaPss.X86_64.RsaPublicPrecomputedAllMdHash

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

end VG.Artifacts.RsaPss.X86_64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaPss.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap fun v => RsaPrivateCrtAllMdHash.artifacts v VG.Proof.Variants.MdHash.X86_64.variants) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap fun v => RsaPublicPrecomputedAllMdHash.artifacts v VG.Proof.Variants.MdHash.X86_64.variants)

end VG.Artifacts.RsaPss.X86_64
