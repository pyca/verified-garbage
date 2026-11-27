module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.RsaPss.Arm.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPss.Arm.Inst
import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PSS (RFC 8017) on ARMv7 -/

namespace VG.Artifacts.RsaPss.Arm

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaPss.Arm (OK)

public def artifacts : List (Artifact Arm.target) :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) =>
    if h : OK Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars then [
      Spec.RsaPss.signPrecomputedMdTableApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
          ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
        code := Impl.RsaPss.Arm.Fn.signPrecomputed (Proof.MdHashTable.Arm.fnsOf Proof.MdHashTable.Arm.vars)
          (Proof.HashTable.Arm.fnsOf Proof.HashTable.Arm.vars) (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)
        verified := Proof.RsaPss.Arm.Fn.signPrecomputed h v },
      Spec.RsaPss.verifyPrecomputedMdTableApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
          ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
        code := Impl.RsaPss.Arm.Fn.verifyPrecomputed (Proof.MdHashTable.Arm.fnsOf Proof.MdHashTable.Arm.vars)
          (Proof.HashTable.Arm.fnsOf Proof.HashTable.Arm.vars) (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code
        verified := Proof.RsaPss.Arm.Fn.verifyPrecomputed h v }]
    else []

spec_apis artifacts

end VG.Artifacts.RsaPss.Arm
