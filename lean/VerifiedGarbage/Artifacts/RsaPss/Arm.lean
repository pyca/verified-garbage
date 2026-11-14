module

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
open VG.Proof.RsaPss.Arm (OK signP_ok verify_ok)

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) =>
    if h : OK Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars then [
      Spec.RsaPss.signPrecomputedMdTableApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
          ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
        code := Proof.RsaPss.Arm.Sg.signCodeP Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars v
        stack := 3624
        verified := signP_ok h v },
      Spec.RsaPss.verifyPrecomputedMdTableApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
          ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
        code := Proof.RsaPss.Arm.Vf.verifyCode Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars
          (Proof.Rsa.Arm.pdOfCrt v)
        stack := 240
        verified := verify_ok h (Proof.Rsa.Arm.pdOfCrt v) }]
    else []

end VG.Artifacts.RsaPss.Arm
