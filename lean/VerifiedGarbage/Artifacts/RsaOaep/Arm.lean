module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.RsaOaep.Arm.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaOaep.Arm.Inst
import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-OAEP (RFC 8017) on ARMv7 -/

namespace VG.Artifacts.RsaOaep.Arm

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaOaep.Arm (OK)
open VG.Proof.HashTable.Arm (vars tables)

public def artifacts : List (Artifact Arm.target) :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) =>
    if h : OK vars then [
      Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", tables vars), ("mgf1", tables vars)]
        code := Impl.RsaOaep.Arm.Fn.decryptPrecomputed (Proof.HashTable.Arm.fnsOf vars) (Proof.Rsa.Arm.privNameP v)
          (Proof.Rsa.Arm.privCodeP v)
        verified := Proof.RsaOaep.Arm.Fn.decryptPrecomputed vars h v },
      Spec.RsaOaep.encryptMdTablesApi.artifact Arm.target {
        suffix := v.suffix
        tables := [("hash", tables vars), ("mgf1", tables vars)]
        code := Impl.RsaOaep.Arm.Fn.encryptPrecomputed (Proof.HashTable.Arm.fnsOf vars) (Proof.Rsa.Arm.pdOfCrt v).name
          (Proof.Rsa.Arm.pdOfCrt v).code
        verified := Proof.RsaOaep.Arm.Fn.encryptPrecomputed vars h v }]
    else []

spec_apis artifacts

end VG.Artifacts.RsaOaep.Arm
