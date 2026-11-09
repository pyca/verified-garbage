module

public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-DSA (FIPS 204) on 32-bit ARM: signing messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.Arm

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign44Fn
      (List.mem_cons_self ..) },
  Spec.MlDsa.signMessage65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign65Fn
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  Spec.MlDsa.signMessage87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign87Fn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
      (Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedSignMessage_verified
      (Proof.MlDsa.Arm.Message.signPreparedFn (.inl rfl)) (List.mem_cons_self ..) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
      (Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedSignMessage_verified
      (Proof.MlDsa.Arm.Message.signPreparedFn (.inr (.inl rfl))) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
      (Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedSignMessage_verified
      (Proof.MlDsa.Arm.Message.signPreparedFn (.inr (.inr rfl)))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsaSignMessage.Arm
