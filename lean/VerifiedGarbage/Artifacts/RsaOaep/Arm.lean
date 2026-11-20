module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.Arm.Inst
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm

/-! # RSAES-OAEP (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.Arm

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaOaep.Arm (OK)
open VG.Proof.HashTable.Arm (vars tables)

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) =>
    if h : OK vars then [
      Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", tables vars), ("mgf1", tables vars)]
        code := Impl.RsaOaep.Arm.Fn.decryptPrecomputed (Proof.HashTable.Arm.fnsOf vars) (Proof.Rsa.Arm.privNameP v)
          (Proof.Rsa.Arm.privCodeP v)
        verified := .scrubbed (Proof.RsaOaep.Arm.Fn.decryptPrecomputed vars h v) },
      Spec.RsaOaep.encryptMdTablesApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", tables vars), ("mgf1", tables vars)]
        code := Impl.RsaOaep.Arm.Fn.encryptPrecomputed (Proof.HashTable.Arm.fnsOf vars) (Proof.Rsa.Arm.pdOfCrt v).name
          (Proof.Rsa.Arm.pdOfCrt v).code
        verified := .scrubbed (Proof.RsaOaep.Arm.Fn.encryptPrecomputed vars h v) }]
    else []

end VG.Artifacts.RsaOaep.Arm
