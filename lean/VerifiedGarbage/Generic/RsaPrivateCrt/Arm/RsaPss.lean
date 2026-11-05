module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.Arm.Inst
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.TCB.Arm.Print

/-! # RSASSA-PSS on ARMv7, with the hash function and MGF1's as tables -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPss

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaPss.Arm (OK sign_ok verify_ok)

def artifacts (v : CrtImpl) : List Artifact :=
  if h : OK Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars then [
    Spec.RsaPss.signTableApi.artifact Arm.target {
      suffix := v.suffix
      tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
        ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
      code := Proof.RsaPss.Arm.Sg.signCode Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars v
      stack := 3624
      verified := sign_ok h v
      features := v.features },
    Spec.RsaPss.verifyPrecomputedTableApi.artifact Arm.target {
      suffix := v.suffix
      tables := [("hash", Proof.MdHashTable.Arm.tables Proof.MdHashTable.Arm.vars),
        ("mgf1", Proof.HashTable.Arm.tables Proof.HashTable.Arm.vars)]
      code := Proof.RsaPss.Arm.Vf.verifyCode Proof.MdHashTable.Arm.vars Proof.HashTable.Arm.vars
        (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := verify_ok h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features }]
  else []

end VG.Generic.RsaPrivateCrt.Arm.RsaPss
