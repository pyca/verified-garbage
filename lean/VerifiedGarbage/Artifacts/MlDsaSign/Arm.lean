module

public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks

/-! # ML-DSA (FIPS 204) signing on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.Arm

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.Sign.sign44_verified' },
  Spec.MlDsa.sign65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.Sign.sign65_verified' },
  Spec.MlDsa.sign87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.Sign.sign87_verified' },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.Message.externalSign_verified (List.mem_cons_self ..) },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.Message.externalSign_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.Message.externalSign_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsaSign.Arm
