module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSASSA-PSS (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPss.PPC64LE

open VG.Proof.RsaPss.PPC64LE (OK verify_ok' sign_ok')
open VG.Proof.MdHashTable.PPC64LE (mvars tables fnsOf fns3)

def artifacts : List Artifact :=
  if h : OK mvars mvars then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact PPC64LE.target {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaPss.PPC64LE.verifyPrecomputed (fnsOf mvars) (fns3 mvars)
      stack := 304
      verified := verify_ok' h },
    Spec.RsaPss.signMdTableApi.artifact PPC64LE.target {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaPss.PPC64LE.Sign.sign (fnsOf mvars) (fns3 mvars)
      stack := 3776
      verified := sign_ok' h }]
  else []

end VG.Artifacts.RsaPss.PPC64LE
