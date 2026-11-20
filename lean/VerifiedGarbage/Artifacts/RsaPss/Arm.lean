module

public import VerifiedGarbage.Proof.RsaPss.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.Arm.Inst
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm

/-! # RSASSA-PSS (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaPss.Arm

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaPss.Arm (OK)

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) =>
    if h : OK Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars then [
      Spec.RsaPss.signPrecomputedMdTableApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
          ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
        code := Impl.RsaPss.Arm.Fn.signPrecomputed (Proof.MdHashTable.Arm.fnsOf Proof.MdHashTable.Arm.vars)
          (Proof.HashTable.Arm.fnsOf Proof.HashTable.Arm.vars) (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)
        verified := .scrubbed (Proof.RsaPss.Arm.Fn.signPrecomputed h v) },
      Spec.RsaPss.verifyPrecomputedMdTableApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
          ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
        code := Impl.RsaPss.Arm.Fn.verifyPrecomputed (Proof.MdHashTable.Arm.fnsOf Proof.MdHashTable.Arm.vars)
          (Proof.HashTable.Arm.fnsOf Proof.HashTable.Arm.vars) (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code
        verified := .scrubbed (Proof.RsaPss.Arm.Fn.verifyPrecomputed h v) }]
    else []

end VG.Artifacts.RsaPss.Arm
