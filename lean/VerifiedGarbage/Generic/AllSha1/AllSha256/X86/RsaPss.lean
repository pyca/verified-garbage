module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Inst

/-! # RSASSA-PSS verification on x86 with a precomputed key, with the hash functions as tables -/

@[expose] public section

namespace VG.Generic.AllSha1.AllSha256.X86.RsaPss

open VG.Proof.RsaPss.X86 (mvars verify_ok)
open VG.Proof.HashTable.X86 (vars)

def artifacts (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    List Artifact :=
  if h : Proof.RsaPss.X86.Sg.OK (mvars vs1 vs256) (vars vs1 vs256) then [
    Spec.RsaPss.verifyPrecomputedTableApi.artifact X86.target {
      suffix := Emit.qualifiedName "" []
      tables := [("hash", Proof.MdHashTable.X86.tables (mvars vs1 vs256)),
        ("mgf1", Proof.HashTable.X86.tables (vars vs1 vs256))]
      code := Proof.RsaPss.X86.Vf.verifyCode (mvars vs1 vs256) (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaPss.X86.Vf.stackBytes
      verified := verify_ok _ _ h Proof.RsaPkcs1Sig.X86.Ver.baseline
      spSafe := Proof.RsaPss.X86.Vf.code_sp h Proof.RsaPkcs1Sig.X86.Ver.baseline
      features := [] }]
  else []

end VG.Generic.AllSha1.AllSha256.X86.RsaPss
