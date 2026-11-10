module

public import VerifiedGarbage.Proof.RsaPss.X86.SgPrecomputed
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Inst
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSASSA-PSS (RFC 8017) on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPss.X86.AllSha1AllSha256

open VG.Proof.RsaPss.X86 (verify_ok)
open VG.Proof.MdHashTable.X86 (mvars)
open VG.Proof.HashTable.X86 (vars)

def artifacts (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    List Artifact :=
  if h : Proof.RsaPss.X86.Sg.OK (mvars vs1 vs256) (vars vs1 vs256) then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact X86.target {
      suffix := qualifiedName "" []
      tables := [("hash", Proof.MdHashTable.X86.tables (mvars vs1 vs256)),
        ("mgf1", Proof.HashTable.X86.tables (vars vs1 vs256))]
      code := Proof.RsaPss.X86.Vf.verifyCode (mvars vs1 vs256) (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaPss.X86.Vf.stackBytes
      verified := verify_ok _ _ h Proof.RsaPkcs1Sig.X86.Ver.baseline
      spSafe := Proof.RsaPss.X86.Vf.code_sp h Proof.RsaPkcs1Sig.X86.Ver.baseline }]
  else []

end VG.Artifacts.RsaPss.X86.AllSha1AllSha256

-- RSASSA-PSS signing on x86, with the hash functions as tables
namespace VG.Artifacts.RsaPss.X86.RsaPrivateCrtAllSha1AllSha256

open VG.Proof.RsaPss.X86 (sign_ok)
open VG.Proof.MdHashTable.X86 (mvars)
open VG.Proof.HashTable.X86 (vars)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if h : Proof.RsaPss.X86.Sg.OK (mvars vs1 vs256) (vars vs1 vs256) then [
    Spec.RsaPss.signMdTableApi.artifact X86.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86.tables (mvars vs1 vs256)),
        ("mgf1", Proof.HashTable.X86.tables (vars vs1 vs256))]
      code := Proof.RsaPss.X86.Sg.signCode (mvars vs1 vs256) (vars vs1 vs256) c
      stack := Proof.RsaPss.X86.Sg.stackBytes
      verified := sign_ok _ _ h c
      spSafe := Proof.RsaPss.X86.Sg.code_sp h c },
    Spec.RsaPss.signPrecomputedMdTableApi.artifact X86.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86.tables (mvars vs1 vs256)),
        ("mgf1", Proof.HashTable.X86.tables (vars vs1 vs256))]
      code := Proof.RsaPss.X86.Sg.signCode (mvars vs1 vs256) (vars vs1 vs256) c
      stack := Proof.RsaPss.X86.Sg.stackBytes
      verified := Proof.RsaPss.X86.Sg.signPrecomputed_verified h c
      spSafe := Proof.RsaPss.X86.Sg.code_sp h c }]
  else []

end VG.Artifacts.RsaPss.X86.RsaPrivateCrtAllSha1AllSha256

namespace VG.Artifacts.RsaPss.X86

def artifacts : List Artifact :=
  AllSha1AllSha256.artifacts VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v => RsaPrivateCrtAllSha1AllSha256.artifacts v VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants)

end VG.Artifacts.RsaPss.X86
