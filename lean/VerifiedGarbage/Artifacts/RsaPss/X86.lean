module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPss.X86.Scrub
import VerifiedGarbage.Impl.RsaPss.X86.Fn
import VerifiedGarbage.Proof.RsaPss.X86.Inst
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PSS (RFC 8017) on x86 -/

namespace VG.Artifacts.RsaPss.X86.AllSha1AllSha256

open VG.Proof.RsaPss.X86.Scrub (allMVars allVars verify_scrubbed)

def artifacts : List (Artifact X86.target) :=
  if h : Proof.RsaPss.X86.Sg.OK allMVars allVars then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact X86.target {
      suffix := qualifiedName "" []
      tables := [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)]
      code := Impl.RsaPss.X86.Fn.verifyPrecomputed (Proof.MdHashTable.X86.fnsOf allMVars)
        (Proof.HashTable.X86.fnsOf allVars) Proof.RsaPkcs1Sig.X86.Ver.baseline.name
        Proof.RsaPkcs1Sig.X86.Ver.baseline.code
      verified := Proof.RsaPss.X86.Scrub.verify_scrubbed h }]
  else []

end VG.Artifacts.RsaPss.X86.AllSha1AllSha256

-- RSASSA-PSS signing on x86, with the hash functions as tables
namespace VG.Artifacts.RsaPss.X86.RsaPrivateCrtAllSha1AllSha256

open VG.Proof.Rsa.X86.PrivChecked (crtPBaseline privCodeP)
open VG.Proof.RsaPss.X86.Scrub (allMVars allVars sign_scrubbed sign_spSafe)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) : List (Artifact X86.target) :=
  if h : Proof.RsaPss.X86.Sg.OK allMVars allVars then [
    Spec.RsaPss.signPrecomputedMdTableApi.artifact X86.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)]
      code := Impl.RsaPss.X86.Fn.signPrecomputed (Proof.MdHashTable.X86.fnsOf allMVars)
        (Proof.HashTable.X86.fnsOf allVars) (Proof.RsaPss.X86.Sg.privNameP c) (privCodeP c crtPBaseline)
      verified := Proof.RsaPss.X86.Scrub.sign_scrubbed h c
      spSafe := Proof.RsaPss.X86.Scrub.sign_spSafe h c }]
  else []

end VG.Artifacts.RsaPss.X86.RsaPrivateCrtAllSha1AllSha256

namespace VG.Artifacts.RsaPss.X86

public def artifacts : List (Artifact X86.target) :=
  AllSha1AllSha256.artifacts ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v => RsaPrivateCrtAllSha1AllSha256.artifacts v)

spec_apis artifacts

end VG.Artifacts.RsaPss.X86
