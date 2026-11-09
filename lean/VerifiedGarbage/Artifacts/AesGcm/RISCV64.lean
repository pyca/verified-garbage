module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # AES-GCM (NIST SP 800-38D) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesGcm.RISCV64

open VG.Proof.AesGcm.RISCV64

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init
    stack := 2560
    verified := init_framed },
  Spec.Gcm.streamInitApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 Impl.AesGcm.RISCV64.streamInit
    stack := 4608
    verified := streamInit_framed },
  Spec.Gcm.streamAadApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.AesGcm.RISCV64.streamAad
    stack := 4608
    verified := streamAad_framed },
  Spec.Gcm.streamEncryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamEncrypt
    stack := 4608
    verified := Proof.AesGcm.streamEncrypt_keyed streamEncrypt_framed },
  Spec.Gcm.streamDecryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamDecrypt
    stack := 4608
    verified := Proof.AesGcm.streamDecrypt_keyed streamDecrypt_framed },
  Spec.Gcm.streamFinishApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.AesGcm.RISCV64.streamFinish
    stack := 4608
    verified := Proof.AesGcm.streamFinish_keyed streamFinish_framed },
  Spec.Gcm.streamVerifyApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamVerify
    stack := 4608
    verified := Proof.AesGcm.streamVerify_keyed streamVerify_framed },
  Spec.Gcm.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 Impl.AesGcm.RISCV64.«seal»
    stack := 4624
    verified := Proof.AesGcm.seal_keyed seal_framed },
  Spec.Gcm.openApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesGcm.RISCV64.«open»
    stack := 4640
    verified := Proof.AesGcm.open_keyed open_framed },
  Spec.Gcm.sealGatherApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.SealGather.sealGather
    stack := 4640
    verified := Proof.AesGcm.sealGather_keyed Gather.sealGather_verified },
  Spec.Gcm.openToApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2608 4 Impl.AesGcm.RISCV64.OpenTo.openTo
    stack := 4656
    verified := Proof.AesGcm.openTo_keyed OpenTo.openTo_framed }]

end VG.Artifacts.AesGcm.RISCV64
