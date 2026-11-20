module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Scrub
public import VerifiedGarbage.Impl.RsaPss.X86.Fn
public import VerifiedGarbage.Proof.RsaPss.X86.Inst
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSASSA-PSS (RFC 8017) on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPss.X86.AllSha1AllSha256

open VG.Proof.RsaPss.X86.Scrub (allMVars allVars verifyReg)

def artifacts : List Artifact :=
  if h : Proof.RsaPss.X86.Sg.OK allMVars allVars then
    [Spec.RsaPss.verifyPrecomputedMdTableApi.artifact X86.target (verifyReg h)]
  else []

end VG.Artifacts.RsaPss.X86.AllSha1AllSha256

-- RSASSA-PSS signing on x86, with the hash functions as tables
namespace VG.Artifacts.RsaPss.X86.RsaPrivateCrtAllSha1AllSha256

open VG.Proof.Rsa.X86.PrivChecked (crtPBaseline privCodeP)
open VG.Proof.RsaPss.X86.Scrub (allMVars allVars sign_scrubbed sign_spSafe)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) : List Artifact :=
  if h : Proof.RsaPss.X86.Sg.OK allMVars allVars then [
    Spec.RsaPss.signPrecomputedMdTableApi.artifact X86.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)]
      code := Impl.RsaPss.X86.Fn.signPrecomputed (Proof.MdHashTable.X86.fnsOf allMVars)
        (Proof.HashTable.X86.fnsOf allVars) (Proof.RsaPss.X86.Sg.privNameP c) (privCodeP c crtPBaseline)
      verified := .scrubbed (sign_scrubbed h c)
      spSafe := sign_spSafe h c }]
  else []

end VG.Artifacts.RsaPss.X86.RsaPrivateCrtAllSha1AllSha256

namespace VG.Artifacts.RsaPss.X86

def artifacts : List Artifact :=
  AllSha1AllSha256.artifacts ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v => RsaPrivateCrtAllSha1AllSha256.artifacts v)

end VG.Artifacts.RsaPss.X86
